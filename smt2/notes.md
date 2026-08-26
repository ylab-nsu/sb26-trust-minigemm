# Команды для запуска: 
- cvc5 --tlimit-per=60000 1.smt2
- vampire -t 60 --input_syntax smtlib2 1.smt2
- cvc4 --tlimit=60000 1.smt2
- alt-ergo -t 60 1.smt2
 
Если выдаёт unsat, то все хорошо, потому что у лемм отрицание сделали.

# Успешно доказанные леммы:
- z3 timeout=60000 -smt2 3.smt2
