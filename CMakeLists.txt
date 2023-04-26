cmake_minimum_required(VERSION 3.19.0)
project(stella-interpreter VERSION 0.1.0)

set (Stella_Syntax
  src/Stella/Absyn.H
  src/Stella/Absyn.C
  src/Stella/Parser.H
  src/Stella/Parser.C
  src/Stella/ParserError.H
  src/Stella/Printer.H
  src/Stella/Printer.C
  src/Stella/Buffer.H
  src/Stella/Buffer.C
  src/Stella/Bison.H
  src/Stella/Lexer.C
  src/Stella/Skeleton.H
  src/Stella/Skeleton.C
)

set (SRCS
  src/Interpret.cpp
  src/Eval.h
  src/Eval.cpp
  src/TypeCheck.h
  src/TypeCheck.cpp
  # src/VisitTypeCheck.h
  # src/VisitTypeCheck.cpp
)

add_executable(stella-interpreter ${Stella_Syntax} ${SRCS})
set_property(TARGET stella-interpreter PROPERTY CXX_STANDARD 17)

set(CPACK_PROJECT_NAME ${PROJECT_NAME})
set(CPACK_PROJECT_VERSION ${PROJECT_VERSION})
include(CPack)

include(CTest)

add_test(NAME applying-non-function-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/applying-non-function-1.stella)
add_test(NAME applying-non-function-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/applying-non-function-2.stella)
add_test(NAME applying-non-function-3 COMMAND stella-interpreter typecheck ../tests/ill-typed/applying-non-function-3.stella)
add_test(NAME argument-type-mismatch-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/argument-type-mismatch-1.stella)
add_test(NAME argument-type-mismatch-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/argument-type-mismatch-2.stella)
add_test(NAME argument-type-mismatch-3 COMMAND stella-interpreter typecheck ../tests/ill-typed/argument-type-mismatch-3.stella)
add_test(NAME bad-if-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-if-1.stella)
add_test(NAME bad-if-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-if-2.stella)
add_test(NAME bad-succ-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-succ-1.stella)
add_test(NAME bad-succ-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-succ-2.stella)
add_test(NAME bad-succ-3 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-succ-3.stella)
add_test(NAME shadowed-variable-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/shadowed-variable-1.stella)
add_test(NAME undefined-variable-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/undefined-variable-1.stella)
add_test(NAME undefined-variable-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/undefined-variable-2.stella)
add_test(NAME bad-squares-1 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-squares-1.stella)
add_test(NAME bad-squares-2 COMMAND stella-interpreter typecheck ../tests/ill-typed/bad-squares-2.stella)
set_tests_properties(
  bad-squares-1
  bad-squares-2
  applying-non-function-1
  applying-non-function-2
  applying-non-function-3
  argument-type-mismatch-1
  argument-type-mismatch-2
  argument-type-mismatch-3
  bad-if-1
  bad-if-2
  bad-succ-1
  bad-succ-2
  bad-succ-3
  shadowed-variable-1
  undefined-variable-1
  undefined-variable-2
  PROPERTIES WILL_FAIL TRUE)

add_test(NAME factorial COMMAND stella-interpreter typecheck ../tests/well-typed/factorial.stella)
add_test(NAME increment_twice COMMAND stella-interpreter typecheck ../tests/well-typed/increment_twice.stella)
add_test(NAME higher-order-1 COMMAND stella-interpreter typecheck ../tests/well-typed/higher-order-1.stella)
add_test(NAME logical-operators COMMAND stella-interpreter typecheck ../tests/well-typed/logical-operators.stella)
add_test(NAME squares COMMAND stella-interpreter typecheck ../tests/well-typed/squares.stella)
