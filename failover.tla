------------------------------- MODULE failover -------------------------------
EXTENDS TLC, Integers
CONSTANT NULL, INSTANCES, GOD, DEVIL, NODES_MAPPING, NODES_OFFSET

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
        (* Мы ожидаем, что в конечном счете лидером станет первый узел
        такое свойство исходит из перехода end_switch_beat *)
        EventuallyRecover == <>[](leader[1] = TRUE)
    end define;

    (* Процесс отражающий смену лидера внутри репликасета,
    текущее состояние хранится в kingdom masters *)
    fair process SwitchProc = GOD
    variables
        switch_count = 0;
    begin
        switch_beat:
            while switch_count > 0 do
                (* TLC будет моделировать каждый возможный переход *)
                with new_leader \in INSTANCES do
                    stateboard_leader := new_leader;
                end with;
                switch_count := (switch_count - 1)
            end while;
        end_switch_beat:
            (* Возвращаем исходного лидера репликасета
            для того, что бы "в конце концов" лидером определенно
            оказался инстанс с номером 1.
            Без этого невозможно поставить условие конечного восстановления*)
            stateboard_leader := 1;
    end process;

    (* Процесс отражающий за внезапную смерть
    и восстановление инстансов в репликасете *)
    fair process LiveProc \in NODES_MAPPING
    variables
        target_node = self - NODES_OFFSET;
        beat_count = 0;
    begin
        live_beat:
            while beat_count > 0 do
                either
                    (* узел жив (восстановлен если был мертв) *)
                    health[target_node] := TRUE;
                or
                    (* узел мертв (выключен если был жив) *)
                    health[target_node] := FALSE;
                    leader[target_node] := FALSE;
                end either;
                beat_count := (beat_count - 1);
            end while;

        end_live_beat:
            (* Восстанавливаем все узлы кластера *)
            health[target_node] := TRUE;

    end process;

    (* Основные процессы для каждого инстанса
    отвечающие за старт, первичную инициализацию и
    обновление собственного статуса согласно информации
    из хранилища (stateboard_leader) *)
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
                goto get_appointment;
            end if;
    end process;

end algorithm;*)

\* BEGIN TRANSLATION - the hash of the PCal code: PCal-a696d27e8116bb71dd12f4feb84a9a49
VARIABLES health, leader, stateboard_leader, pc

(* define statement *)
AtMostOneMaster == <>[](\A m1, m2 \in INSTANCES: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE))


EventuallyRecover == <>[](leader[1] = TRUE)

VARIABLES switch_count, target_node, beat_count, appointment

vars == << health, leader, stateboard_leader, pc, switch_count, target_node, 
           beat_count, appointment >>

ProcSet == {GOD} \cup (NODES_MAPPING) \cup (INSTANCES)

Init == (* Global variables *)
        /\ health = [h \in INSTANCES |-> FALSE]
        /\ leader = [l \in INSTANCES |-> FALSE]
        /\ stateboard_leader = 1
        (* Process SwitchProc *)
        /\ switch_count = 0
        (* Process LiveProc *)
        /\ target_node = [self \in NODES_MAPPING |-> self - NODES_OFFSET]
        /\ beat_count = [self \in NODES_MAPPING |-> 0]
        (* Process FailoverProc *)
        /\ appointment = [self \in INSTANCES |-> stateboard_leader]
        /\ pc = [self \in ProcSet |-> CASE self = GOD -> "switch_beat"
                                        [] self \in NODES_MAPPING -> "live_beat"
                                        [] self \in INSTANCES -> "die"]

switch_beat == /\ pc[GOD] = "switch_beat"
               /\ IF switch_count > 0
                     THEN /\ \E new_leader \in INSTANCES:
                               stateboard_leader' = new_leader
                          /\ switch_count' = (switch_count - 1)
                          /\ pc' = [pc EXCEPT ![GOD] = "switch_beat"]
                     ELSE /\ pc' = [pc EXCEPT ![GOD] = "end_switch_beat"]
                          /\ UNCHANGED << stateboard_leader, switch_count >>
               /\ UNCHANGED << health, leader, target_node, beat_count, 
                               appointment >>

end_switch_beat == /\ pc[GOD] = "end_switch_beat"
                   /\ stateboard_leader' = 1
                   /\ pc' = [pc EXCEPT ![GOD] = "Done"]
                   /\ UNCHANGED << health, leader, switch_count, target_node, 
                                   beat_count, appointment >>

SwitchProc == switch_beat \/ end_switch_beat

live_beat(self) == /\ pc[self] = "live_beat"
                   /\ IF beat_count[self] > 0
                         THEN /\ \/ /\ health' = [health EXCEPT ![target_node[self]] = TRUE]
                                    /\ UNCHANGED leader
                                 \/ /\ health' = [health EXCEPT ![target_node[self]] = FALSE]
                                    /\ leader' = [leader EXCEPT ![target_node[self]] = FALSE]
                              /\ beat_count' = [beat_count EXCEPT ![self] = (beat_count[self] - 1)]
                              /\ pc' = [pc EXCEPT ![self] = "live_beat"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "end_live_beat"]
                              /\ UNCHANGED << health, leader, beat_count >>
                   /\ UNCHANGED << stateboard_leader, switch_count, 
                                   target_node, appointment >>

end_live_beat(self) == /\ pc[self] = "end_live_beat"
                       /\ health' = [health EXCEPT ![target_node[self]] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << leader, stateboard_leader, switch_count, 
                                       target_node, beat_count, appointment >>

LiveProc(self) == live_beat(self) \/ end_live_beat(self)

die(self) == /\ pc[self] = "die"
             /\ (health[self] = TRUE)
             /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
             /\ UNCHANGED << health, leader, stateboard_leader, switch_count, 
                             target_node, beat_count, appointment >>

get_appointment(self) == /\ pc[self] = "get_appointment"
                         /\ IF health[self] = FALSE
                               THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                                    /\ UNCHANGED appointment
                               ELSE /\ appointment' = [appointment EXCEPT ![self] = (stateboard_leader)]
                                    /\ pc' = [pc EXCEPT ![self] = "apply"]
                         /\ UNCHANGED << health, leader, stateboard_leader, 
                                         switch_count, target_node, beat_count >>

apply(self) == /\ pc[self] = "apply"
               /\ IF health[self] = FALSE
                     THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                          /\ UNCHANGED leader
                     ELSE /\ leader' = [leader EXCEPT ![self] = (appointment[self] = self)]
                          /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
               /\ UNCHANGED << health, stateboard_leader, switch_count, 
                               target_node, beat_count, appointment >>

FailoverProc(self) == die(self) \/ get_appointment(self) \/ apply(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SwitchProc
           \/ (\E self \in NODES_MAPPING: LiveProc(self))
           \/ (\E self \in INSTANCES: FailoverProc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(SwitchProc)
        /\ \A self \in NODES_MAPPING : WF_vars(LiveProc(self))
        /\ \A self \in INSTANCES : WF_vars(FailoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-ce4aa8e14391c60b43057dbe0940ea00
===================================================
