## Команды для запуска:
- Команда для вывода через консоль (версию v2 запускать из соответствующей папки):

  `frama-c -wp -wp-prover "alt-ergo,z3,cvc5,vampire,cvc4,coq" -wp-model "Typed+var+nat+real" -wp-session session-dir -wp-timeout 20 main.c`
- Для вывода с использованием графического интерфейса необходимо изменить команду запуска на `frama-c-gui`, использовав прежние параметры.

## Используемые компоненты:
#### Основной инструмент верификации
- Frama-c version 33.0
#### SMT-решатели:
- Alt-Ergo version 2.6.3
- CVC5 version 1.2.1
- CVC4 version 1.8
- Vampire version 4.5.1
- Z3 version 4.13.4
- Coq version 8.18.0
