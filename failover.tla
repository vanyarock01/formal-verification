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
        stateboard_leader = 1

    define
        (* Если существуют как минимум два живых инстанса
        из одного репликасета и они оба являются людерами одновременно,
        то условие инварианта нарушено *)
        AtMostOneMaster == <>[](\A m1, m2 \in INSTANCES: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE))
        (* SwitchProperty == <>(leader[stateboard_leader] = TRUE) *)
        StableLeaderEventually == <>[](leader[1] = TRUE)
        (* В конце концов репликасет восстановится - появится лидер *)
        EventuallyClusterRecover == <>[](\E m \in INSTANCES: (leader[m] = TRUE))
        
    end define;

    macro InstanceDeath(id)
    begin
        health[id] := FALSE;
        leader[id] := FALSE;
    end macro;

    (* Процесс отражающий смену лидера внутри репликасета,
    текущее состояние хранится в kingdom masters *)
    fair process SwitchProc = GOD
    begin
        step_0: stateboard_leader := 2;
        step_1: stateboard_leader := 1;
        step_3: stateboard_leader := 3;
        step_4: stateboard_leader := 4;
        step_5: stateboard_leader := 1;
    end process;

    (* Процесс отражающий за внезапную смерть
    и восстановление инстансов в репликасете *)
    fair process LiveProc = DEVIL
    begin
        (* start *)
        init:
            with i \in INSTANCES do
                health[i] := TRUE;
            end with;
        (* kill and restore *)
        death_2: InstanceDeath(2);
        death_1: InstanceDeath(1);
        restore_1: health[1] := TRUE;
        restore_2: health[2] := TRUE;
            
    end process;

    (* Основные процессы для каждого инстанса
    отвечающие за старт, первичную инициализацию и
    обновление собственного статуса согласно информации
    из королевства (stateboard_leader) *)

    fair process FailoverProc \in INSTANCES
    variables
        appointment = stateboard_leader;
    begin
        die: await (health[self] = TRUE);

        get_appointment:
            (* гарантируем что ничего не произойдет, если узел отключен *)
            if health[self] = FALSE then
                goto die;
            else
                appointment := (stateboard_leader)
            end if;

        (* применение назначения *)
        apply:
            if health[self] = FALSE then
                goto die;
            else
                leader[self] := (appointment = self);
            end if;
 
        restart_loop:
            goto get_appointment;
    end process;

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES health, leader, stateboard_leader, pc

(* define statement *)
AtMostOneMaster == <>[](\A m1, m2 \in INSTANCES: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE))

StableLeaderEventually == <>[](leader[1] = TRUE)

EventuallyClusterRecover == <>[](\E m \in INSTANCES: (leader[m] = TRUE))

VARIABLE appointment

vars == << health, leader, stateboard_leader, pc, appointment >>

ProcSet == {GOD} \cup {DEVIL} \cup (INSTANCES)

Init == (* Global variables *)
        /\ health = [h \in INSTANCES |-> FALSE]
        /\ leader = [l \in INSTANCES |-> FALSE]
        /\ stateboard_leader = 1
        (* Process FailoverProc *)
        /\ appointment = [self \in INSTANCES |-> stateboard_leader]
        /\ pc = [self \in ProcSet |-> CASE self = GOD -> "step_0"
                                        [] self = DEVIL -> "init"
                                        [] self \in INSTANCES -> "die"]

step_0 == /\ pc[GOD] = "step_0"
          /\ stateboard_leader' = 2
          /\ pc' = [pc EXCEPT ![GOD] = "step_1"]
          /\ UNCHANGED << health, leader, appointment >>

step_1 == /\ pc[GOD] = "step_1"
          /\ stateboard_leader' = 1
          /\ pc' = [pc EXCEPT ![GOD] = "step_3"]
          /\ UNCHANGED << health, leader, appointment >>

step_3 == /\ pc[GOD] = "step_3"
          /\ stateboard_leader' = 3
          /\ pc' = [pc EXCEPT ![GOD] = "step_4"]
          /\ UNCHANGED << health, leader, appointment >>

step_4 == /\ pc[GOD] = "step_4"
          /\ stateboard_leader' = 4
          /\ pc' = [pc EXCEPT ![GOD] = "step_5"]
          /\ UNCHANGED << health, leader, appointment >>

step_5 == /\ pc[GOD] = "step_5"
          /\ stateboard_leader' = 1
          /\ pc' = [pc EXCEPT ![GOD] = "Done"]
          /\ UNCHANGED << health, leader, appointment >>

SwitchProc == step_0 \/ step_1 \/ step_3 \/ step_4 \/ step_5

init == /\ pc[DEVIL] = "init"
        /\ \E i \in INSTANCES:
             health' = [health EXCEPT ![i] = TRUE]
        /\ pc' = [pc EXCEPT ![DEVIL] = "death_2"]
        /\ UNCHANGED << leader, stateboard_leader, appointment >>

death_2 == /\ pc[DEVIL] = "death_2"
           /\ health' = [health EXCEPT ![2] = FALSE]
           /\ leader' = [leader EXCEPT ![2] = FALSE]
           /\ pc' = [pc EXCEPT ![DEVIL] = "death_1"]
           /\ UNCHANGED << stateboard_leader, appointment >>

death_1 == /\ pc[DEVIL] = "death_1"
           /\ health' = [health EXCEPT ![1] = FALSE]
           /\ leader' = [leader EXCEPT ![1] = FALSE]
           /\ pc' = [pc EXCEPT ![DEVIL] = "restore_1"]
           /\ UNCHANGED << stateboard_leader, appointment >>

restore_1 == /\ pc[DEVIL] = "restore_1"
             /\ health' = [health EXCEPT ![1] = TRUE]
             /\ pc' = [pc EXCEPT ![DEVIL] = "restore_2"]
             /\ UNCHANGED << leader, stateboard_leader, appointment >>

restore_2 == /\ pc[DEVIL] = "restore_2"
             /\ health' = [health EXCEPT ![2] = TRUE]
             /\ pc' = [pc EXCEPT ![DEVIL] = "Done"]
             /\ UNCHANGED << leader, stateboard_leader, appointment >>

LiveProc == init \/ death_2 \/ death_1 \/ restore_1 \/ restore_2

die(self) == /\ pc[self] = "die"
             /\ (health[self] = TRUE)
             /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
             /\ UNCHANGED << health, leader, stateboard_leader, appointment >>

get_appointment(self) == /\ pc[self] = "get_appointment"
                         /\ IF health[self] = FALSE
                               THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                                    /\ UNCHANGED appointment
                               ELSE /\ appointment' = [appointment EXCEPT ![self] = (stateboard_leader)]
                                    /\ pc' = [pc EXCEPT ![self] = "apply"]
                         /\ UNCHANGED << health, leader, stateboard_leader >>

apply(self) == /\ pc[self] = "apply"
               /\ IF health[self] = FALSE
                     THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                          /\ UNCHANGED leader
                     ELSE /\ leader' = [leader EXCEPT ![self] = (appointment[self] = self)]
                          /\ pc' = [pc EXCEPT ![self] = "restart_loop"]
               /\ UNCHANGED << health, stateboard_leader, appointment >>

restart_loop(self) == /\ pc[self] = "restart_loop"
                      /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
                      /\ UNCHANGED << health, leader, stateboard_leader, 
                                      appointment >>

FailoverProc(self) == die(self) \/ get_appointment(self) \/ apply(self)
                         \/ restart_loop(self)

Next == SwitchProc \/ LiveProc
           \/ (\E self \in INSTANCES: FailoverProc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(SwitchProc)
        /\ WF_vars(LiveProc)
        /\ \A self \in INSTANCES : WF_vars(FailoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
===================================================
