# Команды для запуска:
- Команда для вывода через консоль:

  `frama-c -wp -wp-prover "alt-ergo,z3,cvc5,vampire,cvc4,coq" -wp-model "Typed+var+nat+real" -wp-session session-dir -wp-timeout 10 gemm/v2/main.c`
- Для вывода с использованием графического интерфейса необходимо изменить команду запуска на "frama-c-gui", использовав прежние параметры.
