------------------------------- MODULE failover -------------------------------
EXTENDS TLC, Integers
CONSTANT NULL, INSTANCES, GOD, DEVIL

(* --algorithm failover

(* Алгоритм **stateful** фейловера подразумевает, что есть внешнее
   хранилище, которое хранит единственное состояние кластера и всем
   остальным предлагается использовать именно его при выборе роли.
   В этом подходе есть узкие места, которые СТОИТ постараться разделить
   +------------------------------------------------------------------+
   1) В хранилище может писать один король (lock)?
   +------------------------------------------------------------------+
   2) Что может пойти не так при множественном чтении из хранилища?
   +------------------------------------------------------------------+
   3) Может ли развалить кластер 1 король захвативший lock?
   +------------------------------------------------------------------+
   ...
   Здесь буду описывать третий сценарий. *)

    variables
        (* здесь хранится реальное текущее состояние для каждого инстанса *)
        health = [h \in INSTANCES |-> FALSE],
        (* здесь хранится реальная текущая роль для каждого инстанса *)
        leader = [l \in INSTANCES |-> FALSE],
        (* выбранный лидер *)
        kingdom_leader = 1

    define
        (* Если существуют как минимум два живых инстанса
        из одного репликасета и они оба являются людерами одновременно,
        то условие инварианта нарушено *)
        AtMostOneMaster == <>[](\A m1, m2 \in INSTANCES: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE))
        (* SwitchProperty == <>(leader[kingdom_leader] = TRUE) *)
        StableLeaderEventually == <>[](leader[1] = TRUE)
        (* В конце концов репликасет восстановится - появится лидер *)
        EventuallyClusterRecover == <>[](\E m \in INSTANCES: (leader[m] = TRUE))
    end define;

    (* Процесс отражающий смену лидера внутри репликасета,
    текущее состояние хранится в kingdom masters *)
    fair process SwitchProc = GOD
    begin
        set_2: kingdom_leader := 2;
        set_1: kingdom_leader := 1;
    end process;

    (* Процесс отражающий за внезапную смерть
    и восстановление инстансов в репликасете *)
    fair process LiveProc = DEVIL
    begin
        kill_2: health[2] := FALSE;
        kill_1: health[1] := FALSE;
        restore_1: health[1] := TRUE;
        restore_2: health[2] := TRUE;
    end process;

    (* Основные процессы для каждого инстанса
    отвечающие за старт, первичную инициализацию и
    обновление собственного статуса согласно информации
    из королевства (kingdom_leader) *)
    fair process FailoverProc \in INSTANCES
    begin
        (* Каждый инстанс запускается *)
        born: health[self] := TRUE;
        (* И принимает на себя роль в первый раз *)
        init: leader[self] := (kingdom_leader = self);
        
        continue_loop: skip;
        die:
            if (health[self] = FALSE) then goto continue_loop; end if;
        apply:
            leader[self] := (kingdom_leader = self);

        restart_loop:
            goto continue_loop;
    end process;

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES health, leader, kingdom_leader, pc

(* define statement *)
AtMostOneMaster == <>[](\A m1, m2 \in INSTANCES: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE))

StableLeaderEventually == <>[](leader[1] = TRUE)

EventuallyClusterRecover == <>[](\E m \in INSTANCES: (leader[m] = TRUE))


vars == << health, leader, kingdom_leader, pc >>

ProcSet == {GOD} \cup {DEVIL} \cup (INSTANCES)

Init == (* Global variables *)
        /\ health = [h \in INSTANCES |-> FALSE]
        /\ leader = [l \in INSTANCES |-> FALSE]
        /\ kingdom_leader = 1
        /\ pc = [self \in ProcSet |-> CASE self = GOD -> "set_2"
                                        [] self = DEVIL -> "kill_2"
                                        [] self \in INSTANCES -> "born"]

set_2 == /\ pc[GOD] = "set_2"
         /\ kingdom_leader' = 2
         /\ pc' = [pc EXCEPT ![GOD] = "set_1"]
         /\ UNCHANGED << health, leader >>

set_1 == /\ pc[GOD] = "set_1"
         /\ kingdom_leader' = 1
         /\ pc' = [pc EXCEPT ![GOD] = "Done"]
         /\ UNCHANGED << health, leader >>

SwitchProc == set_2 \/ set_1

kill_2 == /\ pc[DEVIL] = "kill_2"
          /\ health' = [health EXCEPT ![2] = FALSE]
          /\ pc' = [pc EXCEPT ![DEVIL] = "kill_1"]
          /\ UNCHANGED << leader, kingdom_leader >>

kill_1 == /\ pc[DEVIL] = "kill_1"
          /\ health' = [health EXCEPT ![1] = FALSE]
          /\ pc' = [pc EXCEPT ![DEVIL] = "restore_2"]
          /\ UNCHANGED << leader, kingdom_leader >>

restore_2 == /\ pc[DEVIL] = "restore_2"
             /\ health' = [health EXCEPT ![2] = TRUE]
             /\ pc' = [pc EXCEPT ![DEVIL] = "restore_1"]
             /\ UNCHANGED << leader, kingdom_leader >>

restore_1 == /\ pc[DEVIL] = "restore_1"
             /\ health' = [health EXCEPT ![1] = TRUE]
             /\ pc' = [pc EXCEPT ![DEVIL] = "Done"]
             /\ UNCHANGED << leader, kingdom_leader >>

LiveProc == kill_2 \/ kill_1 \/ restore_2 \/ restore_1

born(self) == /\ pc[self] = "born"
              /\ health' = [health EXCEPT ![self] = TRUE]
              /\ pc' = [pc EXCEPT ![self] = "init"]
              /\ UNCHANGED << leader, kingdom_leader >>

init(self) == /\ pc[self] = "init"
              /\ leader' = [leader EXCEPT ![self] = (kingdom_leader = self)]
              /\ pc' = [pc EXCEPT ![self] = "continue_loop"]
              /\ UNCHANGED << health, kingdom_leader >>

continue_loop(self) == /\ pc[self] = "continue_loop"
                       /\ TRUE
                       /\ pc' = [pc EXCEPT ![self] = "die"]
                       /\ UNCHANGED << health, leader, kingdom_leader >>

die(self) == /\ pc[self] = "die"
             /\ IF (health[self] = FALSE)
                   THEN /\ pc' = [pc EXCEPT ![self] = "continue_loop"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "apply"]
             /\ UNCHANGED << health, leader, kingdom_leader >>

apply(self) == /\ pc[self] = "apply"
               /\ leader' = [leader EXCEPT ![self] = (kingdom_leader = self)]
               /\ pc' = [pc EXCEPT ![self] = "restart_loop"]
               /\ UNCHANGED << health, kingdom_leader >>

restart_loop(self) == /\ pc[self] = "restart_loop"
                      /\ pc' = [pc EXCEPT ![self] = "continue_loop"]
                      /\ UNCHANGED << health, leader, kingdom_leader >>

FailoverProc(self) == born(self) \/ init(self) \/ continue_loop(self)
                         \/ die(self) \/ apply(self) \/ restart_loop(self)

Next == SwitchProc \/ LiveProc
           \/ (\E self \in INSTANCES: FailoverProc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(LiveProc)
        /\ \A self \in INSTANCES : WF_vars(FailoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
===================================================
