# Используемые компоненты
## Платформа для анализа и верификации программ
- Frama-С 33.0
## Автоматические доказатели теорем (в том числе SMT-решатели)
- Alt-Ergo 2.6.3
- [CVC5 1.2.1](https://github.com/cvc5/cvc5/releases/download/cvc5-1.2.1/cvc5-Linux-x86_64-static.zip)
- CVC4 1.8
- [Vampire 4.5.1](https://github.com/vprover/vampire/releases/download/4.5.1/vampire_z3_Release_static_master_4764.zip)
- [Z3 4.13.4](https://github.com/Z3Prover/z3/releases/download/z3-4.13.4/z3-4.13.4-x64-glibc-2.35.zip)
## Интерактивные доказатели теорем
- Coq (ныне Rocq) 8.20.1

# Установка необходимых программ
## Debian и Ubuntu GNU/Linux
### opam, Coq, Frama-C, Alt-Ergo, Why3
1. Установите пакетный менеджер [opam](https://opam.ocaml.org/doc/Install.html).
2. Установите необходимые пакеты следующей командой: `opam install -y coq coqide alt-ergo why3 why3-coq coq-simple-io coq-quickchick coq-hammer coq-hammer-tactics coq-core frama-c`. Важно, что пакеты устанавливаются одной пачкой, так как иначе возникнет куча конфликтов версий.
### GUI для Frama-C
3. Подайте команду `frama-c-gui`. При первом запуске Вам будет показана инструкция по установке. Зафиксируйте номер версии Node.js. Первым шагом [установите NVM](https://github.com/nvm-sh/nvm#installing-and-updating).
4. Далее для установки и активации Node.js подайте команду `nvm install 24 && nvm use 24 && npm install --global yarn`. Номер версии может быть другим (на момент написания это 24), смотрите инструкцию, выданную `frama-c-gui`.
5. Теперь снова подайте команду `frama-c-gui`, и тем самым соберётся графическая оболочка для Frama-C. Если Node.js после этого не нужен, его можно спокойно удалить с компьютера.
### Z3, CVC4, CVC5, Vampire
6. Легче всех устанавливается CVC4: `sudo apt-get install cvc4`.
7. Why3, который служит "мостом" между Frama-C и доказателями теорем, привередлив к версиям последних, поэтому не спешите ставить самые новые. На момент написания этой инструкции номера совместимых версий представлены в списке выше. По вложенным ссылкам скачайте соответствующие версии Z3, CVC5 и Vampire.
8. Распакуйте и положите директории, например, в домашнюю папку.
9. Откройте файл `~/.bashrc` и к самому концу файла припишите следующую строку: `export PATH="~/prover/bin:$PATH"`, где `prover` - имя директории, в которой лежит доказатель. Данный процесс проделайте для каждого из трёх. Если у Вас запущены терминалы, подайте в каждом из них команду `source ~/.bashrc`, или просто перезапустите их. Этим шагом Вы дадите системе знать, где лежат исполняемые файлы каждого из доказателей. Важно: исполняемый файл доказателя Vampire необходимо переименовать в `vampire`.
### Проверка
10. Чтобы убедиться, что всё получилось, подайте команду `why3 config detect`. Если всё получилось, то на выходе будут перечислены все доказатели с соответствующими версиями и надписями "OK".

## Microsoft Windows
Используйте Ubuntu через WSL.

# Команды для запуска
Версию v2 необходимо запускать из соответствующей папки.
- Команда для верификации в терминале:
  `frama-c -wp -wp-prover "alt-ergo,z3,cvc5,vampire,cvc4,coq" -wp-model "Typed+var+nat+real" -wp-session session-dir -wp-timeout 20 main.c`
- Команда для верификации в графической оболочке:
  `frama-c-gui -wp -wp-prover "alt-ergo,z3,cvc5,vampire,cvc4,coq" -wp-model "Typed+var+nat+real" -wp-session session-dir -wp-timeout 20 main.c`
