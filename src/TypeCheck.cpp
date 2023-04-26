#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <cassert>
#include <unordered_map>
#include "TypeCheck.h"
#include "Stella/Skeleton.H"
#include "Stella/Absyn.H"

using namespace std;

namespace Stella
{
    string toString(Type *type);

    string toString(ListType *list_type){
        string result = "";
        for (ListType::iterator it = list_type->begin(); it != list_type->end(); it++)
            result +=  (it == list_type->begin() ? "" : ",") + toString(*it);
        return result;
    }

    string toString(Type *type)
    {
        static long long nullCounter = 0;
        if (type == nullptr)
            return "NULL<" + to_string(nullCounter++) + ">";

        if (auto type_bool = dynamic_cast<TypeBool *>(type))
            return "Bool";
    
        if (auto type_nat = dynamic_cast<TypeNat *>(type))
            return "Nat";
        
        if (auto type_unit = dynamic_cast<TypeUnit *>(type))
            return "Unit";
        
        if (auto type_ref = dynamic_cast<TypeRef *>(type))
          return "&" + toString(type_ref->type_);

        if (auto type_tuple = dynamic_cast<TypeTuple *>(type))
            return "{" + toString(type_tuple->listtype_) + "}";
        
        if (auto type_fun = dynamic_cast<TypeFun *>(type))
            return "(" + toString(type_fun->listtype_) + ")->(" + toString(type_fun->type_) + ")";
        
        if (auto type_sum = dynamic_cast<TypeSum *>(type))
            return "(" + toString(type_sum->type_1) + "+" + toString(type_sum->type_2) + ")";

        throw invalid_argument("Type is not implemented");
    }

    TypeFun *extractType(DeclFun *decl_fun)
    {
        auto list_param_decl = decl_fun->listparamdecl_;
        auto return_type = decl_fun->returntype_;
        auto list_type = new ListType();
        for (ListParamDecl::iterator i = list_param_decl->begin(); i != list_param_decl->end(); i++){
            list_type->push_back(dynamic_cast<AParamDecl *>(*i)->type_);
        }
        Type *type = nullptr;
        if (auto some_return_type = dynamic_cast<SomeReturnType *>(return_type)){
            type = some_return_type->type_;
        }
        return new TypeFun(list_type, type);
    }

    bool typecheck(Type *type1, Type *type2)
    {
        return toString(type1) == toString(type2);
    }

    string colorize(string text, int code)
    {
        return "\033[1;" + to_string(30 + code % 8) + "m" + text + "\033[1;0m";
    }

    string putTab(int cnt)
    {
        string res = "";
        for (int i = 1; i < cnt; i++)
            res += colorize("| ", i);
        return res;
    }
    string beautify(string text, int depth)
    {
        return putTab(depth) + colorize(text, depth);
    }

    class TypeError: public exception
    {
        private:
            string msg;
        public:
            TypeError(Type* e_type, Type* a_type, int r, int c)
                :msg(
                    "TypeError (" + to_string(r) + ", " + to_string(c) + "): " + 
                    "Expected " + toString(e_type) + " type but got " + toString(a_type) + " type."
                ){}
            TypeError(string e_type, string a_type, int r, int c)
                :msg(
                    "TypeError (" + to_string(r) + ", " + to_string(c) + "): " + 
                    "Expected " + e_type + " type but got " + a_type + " type."
                ){}
            TypeError(string text, int r, int c)
                :msg(
                    "TypeError (" + to_string(r) + ", " + to_string(c) + "): " + text
                ){}
            const char* what() const noexcept override{return msg.c_str();}
    };


    class UndefinedError: public exception
    {
        private:
            string msg;
        public:
            UndefinedError(string var_name, int r, int c)
                :msg(
                    "UndefinedError (" + to_string(r) + ", " + to_string(c) + "): " + 
                    var_name + " is not defined in this scope."
                ){}
            const char* what() const noexcept override{return msg.c_str();}
    };


    class VisitTypeCheck : public Skeleton
    {
    public:
        string message_outputs = "";

    private:
        unordered_map<StellaIdent, Type *> context = {};
        Type *expected_type = nullptr;
        Type *actual_type = nullptr;
        Type *match_type = nullptr;
        int visitDepth = 0;

        void enterVisit() { this->visitDepth++; }
        void exitVisit() { this->visitDepth--; }

        void logMessage(string text)
        {
            cout << beautify(text, this->visitDepth) << endl;
            message_outputs += beautify(text, this->visitDepth) + "\n";
        }

        unordered_map<StellaIdent, Type *> enter_scope(ListParamDecl *list_param_decl)
        {
            unordered_map<StellaIdent, Type *> old_context(context.begin(), context.end());
            for (auto param : (*list_param_decl)){
                if (auto a_param = dynamic_cast<AParamDecl*>(param))
                    context[a_param->stellaident_] = a_param->type_;
                else
                    throw invalid_argument("ParamDecl is not implemented");
            }
            return old_context;
        }

        void exit_scope(unordered_map<StellaIdent, Type *> old_context)
        {
            context = old_context;
        }

        void set_actual_type(Expr *expr, Type *type)
        {
            if(expected_type != nullptr && !typecheck(expected_type, type)){
                throw TypeError(toString(expected_type), toString(type), expr->line_number, expr->char_number);
            }
            actual_type = type;
        }

        Type *typecheck_subexpr(Expr *expr, Type *type)
        {
            Type *old_expected_type = expected_type;
            expected_type = type;
            expr->accept(this);
            expected_type = old_expected_type;
            return actual_type;
        }

        void typecheck_pattern(Pattern *pattern, Type *type)
        {
            Type *old_match_type = match_type;
            match_type = type;
            pattern->accept(this);
            match_type = old_match_type; 
        }

        // void visitDeref(Deref *deref)
        // {
        //   enterVisit();
        //   logMessage("visitDeref; expected_type: " + toString(expected_type));
        //   auto expr_type = typecheck_subexpr(deref->expr_, nullptr);
        //   if(auto type_ref = dynamic_cast<TypeRef *>(expr_type)){
        //     set_actual_type();
        //   }
        //   else{
        //     TypeError()
        //   }




        //   exitVisit();
        // }

        void visitSequence(Sequence *sequence)
        {
            enterVisit();
            logMessage("visitSequence; exptected_type: " + toString(expected_type));
            typecheck_subexpr(sequence->expr_1, new TypeUnit());
            logMessage("+-------------------------");
            sequence->expr_2->accept(this);
            exitVisit();
        }

        void visitSucc(Succ *succ)
        {
            enterVisit();
            logMessage("visitSucc; expected_type: " + toString(expected_type));
            typecheck_subexpr(succ->expr_, new TypeNat());
            set_actual_type(succ, new TypeNat());
            exitVisit();
        }

        void visitNatRec(NatRec *nat_rec)
        {
            enterVisit();
            logMessage("visitNatRec; expected_type: " + toString(expected_type));
            typecheck_subexpr(nat_rec->expr_1, new TypeNat());
            
            logMessage("+-------------------------");
            auto expr2_type = typecheck_subexpr(nat_rec->expr_2, nullptr);

            logMessage("+-------------------------");
            typecheck_subexpr(nat_rec->expr_3, 
                new TypeFun(
                    consListType(new TypeNat(), new ListType()), 
                    new TypeFun(
                        consListType(expr2_type, new ListType()),
                        expr2_type
                    )
                )
            );
            set_actual_type(nat_rec, expr2_type);
            exitVisit();
        }

        void visitConstInt(ConstInt *const_int)
        {
            enterVisit();
            logMessage("visitConstInt: " + to_string(const_int->integer_) + "; expected_type: " + toString(expected_type));
            set_actual_type(const_int, new TypeNat());
            exitVisit();
        }

        void visitConstTrue(ConstTrue *const_true)
        {
            enterVisit();
            logMessage("visitConstTrue; expected_type: " + toString(expected_type));
            set_actual_type(const_true, new TypeBool);
            exitVisit();
        }

        void visitConstFalse(ConstFalse *const_false)
        {
            enterVisit();
            logMessage("visitConstFalse; expected_type: " + toString(expected_type));
            set_actual_type(const_false, new TypeBool());
            exitVisit();
        }

        void visitConstUnit(ConstUnit *const_unit)
        {
            enterVisit();
            logMessage("visitConstUnit; expected_type: " + toString(expected_type));
            set_actual_type(const_unit, new TypeUnit());
            exitVisit();
        }

        void visitVar(Var *var)
        {
            enterVisit();
            logMessage("visitVar: " + var->stellaident_ + "; expected_type: " + toString(expected_type));
            if(context.find(var->stellaident_) == context.end())
                throw UndefinedError(var->stellaident_, var->line_number, var->char_number);
            set_actual_type(var, context[var->stellaident_]);
            exitVisit();
        }

        void visitTuple(Tuple *tuple)
        {
            enterVisit();
            logMessage("vistTuple; expected_tuple: " + toString(expected_type));
            auto list_type = new ListType();
            auto list_expr = tuple->listexpr_;
            for(ListExpr::iterator it = list_expr->begin(); it != list_expr->end(); it ++)
                list_type->push_back(typecheck_subexpr(*it, nullptr));

            set_actual_type(tuple, new TypeTuple(list_type));
            exitVisit();
        }

        void visitDotTuple(DotTuple *dot_tuple)
        {
            enterVisit();
            logMessage("visitDotTuple; expected_tuple: " + toString(expected_type));
            auto expr = dot_tuple->expr_;
            auto expr_type = typecheck_subexpr(dot_tuple->expr_, nullptr);
            if(auto type_tuple = dynamic_cast<TypeTuple *>(expr_type)){
                auto list_type = type_tuple->listtype_;
                if(list_type->size() < dot_tuple->integer_)
                    throw TypeError(
                        "Tuple has only " + to_string(list_type->size()) + " fields but " + to_string(dot_tuple->integer_) + "th is accessed",
                        dot_tuple->line_number, dot_tuple->char_number);
                set_actual_type(dot_tuple, list_type->at(dot_tuple->integer_ - 1));
            }
            else{
                throw TypeError(
                    "Expected Tuple type but got " + toString(expr_type) + " type", expr->line_number, expr->char_number
                );
            }
            exitVisit();
        }

        void visitInl(Inl *inl)
        {
            enterVisit();
            logMessage("visitInl; expected_type: " + toString(expected_type));
            if(auto type_sum=dynamic_cast<TypeSum*>(expected_type)){
                actual_type = typecheck_subexpr(inl->expr_, type_sum->type_1);
            }
            else{
                throw TypeError(toString(expected_type), "TypeSum", inl->line_number, inl->char_number);
            }
            exitVisit();
        }

        void visitInr(Inr *inr)
        {
            enterVisit();
            logMessage("visitInr; expected_type: " + toString(expected_type));
            if(auto type_sum=dynamic_cast<TypeSum*>(expected_type)){
                actual_type = typecheck_subexpr(inr->expr_, type_sum->type_2);
            }
            else{
                throw TypeError(toString(expected_type), "TypeSum", inr->line_number, inr->char_number);
            }
            exitVisit();
        }

        void visitPatternInl(PatternInl *pattern_inl)
        {
            enterVisit();
            logMessage("visitPatternInl; match_type:" + toString(match_type) + ";  expected_type: " + toString(expected_type));
            if(auto type_sum = dynamic_cast<TypeSum *>(match_type))
                typecheck_pattern(pattern_inl->pattern_, type_sum->type_1);
            else
                throw TypeError("PatternInr requires TypeSum in match case", pattern_inl->line_number, pattern_inl->char_number);
            exitVisit();
        }

        void visitPatternInr(PatternInr *pattern_inr)
        {
            enterVisit();
            logMessage("visitPatternInr; match_type:" + toString(match_type) + ";  expected_type: " + toString(expected_type));
            if(auto type_sum = dynamic_cast<TypeSum *>(match_type))
                typecheck_pattern(pattern_inr->pattern_, type_sum->type_2);
            else
                throw TypeError("PatternInr requires TypeSum in match case", pattern_inr->line_number, pattern_inr->char_number);
            exitVisit();
        }
        
        void visitPatternVar(PatternVar *pattern_var)
        {
            enterVisit();
            logMessage("visitPatternVar: " + pattern_var->stellaident_ + "; match_type:" + toString(match_type) + ";  expected_type: " + toString(expected_type));
            context[pattern_var->stellaident_] = match_type;
            exitVisit();
        }

        void visitMatch(Match *match)
        {
            enterVisit();
            logMessage("visitMatch; list_match_case_size: " + to_string(match->listmatchcase_->size()) + ";expected_type: " + toString(expected_type));
            auto expr_type = typecheck_subexpr(match->expr_, nullptr);
            auto list_case = match->listmatchcase_;
            
            for(ListMatchCase::iterator it = list_case->begin(); it != list_case->end(); it ++){
                auto a_match_case = dynamic_cast<AMatchCase*>(*it);
                typecheck_pattern(a_match_case->pattern_, expr_type);
                typecheck_subexpr(a_match_case->expr_, expected_type);
            }
            exitVisit();
        }

        void visitIf(If *if_)
        {
            enterVisit();
            logMessage("visitIf; expected_type: " + toString(expected_type));
            typecheck_subexpr(if_->expr_1, new TypeBool());
            logMessage("+-------------------------");
            auto expr2_type = typecheck_subexpr(if_->expr_2, expected_type);
            logMessage("+-------------------------");
            if( expected_type == nullptr ){
                typecheck_subexpr(if_->expr_3, expr2_type);
                set_actual_type(if_, expr2_type);
            }
            else{
                typecheck_subexpr(if_->expr_3, expected_type);
                set_actual_type(if_, expected_type);
            }
            exitVisit();
        }

        void visitApplication(Application *application)
        {
            enterVisit();
            logMessage("visitApplication; expected_type: " + toString(expected_type));
            auto expr = application->expr_;
            auto expr_type = typecheck_subexpr(expr, nullptr);
            if(auto type_fun = dynamic_cast<TypeFun*>(expr_type)){
                auto list_expr = application->listexpr_;
                auto list_type = type_fun->listtype_;

                if(list_type->size() != list_expr->size()){
                    throw TypeError(
                        "Expected " + to_string(list_type->size()) + " arguments but " + to_string(list_expr->size()) + " were given", 
                        application->line_number, application->char_number
                    );
                }
                auto expr_it = list_expr->begin(); 
                auto type_it = list_type->begin();
                while(expr_it != list_expr->end()){
                    typecheck_subexpr(*expr_it, *type_it);
                    expr_it ++;
                    type_it ++;
                }
                set_actual_type(application, type_fun->type_);                
            }
            else{
                throw TypeError(
                    "Expected function type but got " + toString(expr_type) + " type", expr->line_number, expr->char_number
                );
            }
            exitVisit();
        }

        void visitAbstraction(Abstraction *abstraction)
        {
            enterVisit();
            logMessage("visitAbstraction; expected_type: " + toString(expected_type));
            auto old_context = enter_scope(abstraction->listparamdecl_);
            if(!expected_type){
                auto lt = new ListType();
                auto lp = abstraction->listparamdecl_;
                for(ListParamDecl::iterator it = lp->begin(); it != lp->end(); it ++ )
                    lt->push_back(dynamic_cast<AParamDecl*>(*it)->type_);
                auto expr_type = typecheck_subexpr(abstraction->expr_, nullptr);
                set_actual_type(abstraction, new TypeFun(lt, expr_type));
            }
            else if(auto type_fun=dynamic_cast<TypeFun*>(expected_type)){
                auto lp = abstraction->listparamdecl_;
                auto lt = type_fun->listtype_;
                if(lp->size() != lt->size()){
                    throw TypeError(
                        "Expected function type requires " + to_string(lt->size()) + " arguments but anonymous functions has " + to_string(lp->size()),
                        abstraction->line_number, abstraction->char_number
                    );
                }
                for(int i = 0; i < lp->size(); i ++){
                    auto p = dynamic_cast<AParamDecl*>(lp->at(i));
                    if(!typecheck(lt->at(i), p->type_))
                        throw TypeError(lt->at(i), p->type_, p->line_number, p->char_number);
                }
                typecheck_subexpr(abstraction->expr_, type_fun->type_);
                set_actual_type(abstraction, expected_type);
            }
            else{
                throw TypeError(
                    "Expected " + toString(expected_type) + " type but got anonymous function",
                    abstraction->line_number, abstraction->char_number
                );
            }

            exit_scope(old_context);
            exitVisit();
        }

        void visitDeclFun(DeclFun *decl_fun)
        {
            enterVisit();
            logMessage("visitDeclFun: " + decl_fun->stellaident_);
            auto old_context = enter_scope(decl_fun->listparamdecl_);

            if(auto some_return_type = dynamic_cast<SomeReturnType*>(decl_fun->returntype_))
                typecheck_subexpr(decl_fun->expr_, some_return_type->type_);
            else
                typecheck_subexpr(decl_fun->expr_, nullptr);

            exit_scope(old_context);
            context[decl_fun->stellaident_] = extractType(decl_fun);
            exitVisit();
        }

        void visitAProgram(AProgram *a_program)
        {
            enterVisit();
            logMessage("visitAProgram");
            a_program->listdecl_->accept(this);
            exitVisit();
        }
    };

    void typecheckProgram(Program *program)
    {
        auto visitTypeCheck = new VisitTypeCheck();

        try{
            program->accept(visitTypeCheck);
            cout << visitTypeCheck->message_outputs << endl;

            cout << colorize("Success!!!", 2) << endl << endl;
        }
        catch(TypeError& e){
            cout << endl << colorize(e.what(), 1) << endl << endl;
            exit(1);
        }
        catch(UndefinedError& e){
            cout << endl << colorize(e.what(), 1) << endl << endl;
            exit(1);
        }
    }
}

/*
language core;
extend with #tuples;

fn noop(_ : {}) -> {} {
  return {}
}

fn third(tup : {Nat, Nat, Nat}) -> Nat {
  return tup.4
}

fn main(n : Nat) -> Nat {
  return third({n, succ(n), succ(succ(n))})
}


language core;

extend with #sum-types, #unit-type;

fn test(first : Bool) -> fn (Nat) -> Nat + Unit {
  return fn(n : Nat){ return if first then inl(succ(0)) else inr(unit) }
}



language core;
extend with #sum-types, #structural-patterns;

fn main(input : Nat + (Bool + (fn (Nat) -> Nat))) -> Nat {
  return match input {
        inl(number) => number
      | inr(inl(false)) => 0
      | inr(inl(true)) => succ(0)
      | inr(inr(fun)) => fun(0)(1)
   }
}


language core;
extend with #sum-types;

fn g(x : Nat + (Bool + (fn(Nat) -> Nat))) -> Nat {
  return match x {
      inl(n) => succ(n)
    | inr(bf) => match bf {
          inl(b) => if b then succ(0) else 0
        | inr(f) => f(f(succ(0)))
      }
  }
}

fn main(x : Nat) -> Nat {
  return g(inr(inr(fn(n : Nat) { return g(inl(n)) })))
}



language core;
extend with #sum-types;





*/