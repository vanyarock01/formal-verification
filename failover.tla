------------------------------- MODULE failover -------------------------------
EXTENDS TLC, Integers
CONSTANT NULL, NODES, GOD, DEVIL, NODES_MAPPING, NODES_OFFSET

(* --algorithm failover

(* Полный алгоритм **stateful** фейловера состоит из трех элементов
1. Узлы в репликасете, которые могут иметь 2 роли - ведущий узел(leader[id] = TRUE) и ведомый (leader[id] = FALSE)
2. Координатор который сообщает о состоянии узлов, его поведение моделируется при помощи SwitchProc
3. Внешнее хранилище хранящее единственное представление о состоянии кластера, в нашем случае переменная stateboard_leader

fencing - алгоритм самоограждения узла при потере связи с ? координатором.
Назначеный узел перед тем как *)

    variables
        (* текущее состояние для каждого узла *)
        health = [n \in NODES |-> FALSE],
        (* информация о доступности узла, нужно для моделирования
        ситуаций когда происходит потеря связи с узлом при его фактической доступности*)
        availability = [n \in NODES |-> FALSE],
        (* реальная текущая роль каждого инстанса *)
        leader = [n \in NODES |-> FALSE],
        (* выбранный лидер *)
        stateboard_leader = 1,
        last_accepting_leader = 1
    define
        (* Если существуют как минимум два живых узла
        из одного репликасета и они оба являются людерами одновременно,
        то условие инварианта нарушено *)
        AtMostOneMaster == [](\A n1, n2 \in NODES: (n1 /= n2) => ~(leader[n1] = TRUE /\ leader[n2] = TRUE))
        (* Мы ожидаем, что в конечном счете лидером станет первый узел
        такое свойство исходит из перехода end_switch_beat *)
        EventuallyRecover == <>[](leader[1] = TRUE)
        
    end define;

    macro NodeUp(node_id)
    (* Переводит узел в рабочее состояние и делает его доступным *)
    begin
        health[node_id] := TRUE;
        availability[node_id] := TRUE;
    end macro;

    macro NodeDown(node_id)
    (* Переводит узел в выключенное состояние и делает его недоступным *)
    begin
        health[node_id] := FALSE;
        availability[node_id] := FALSE;
    end macro;

    (* Процесс отражающий смену лидера внутри репликасета,
    текущее состояние хранится в kingdom masters *)
    fair process SwitchProc = GOD
    variables
        switch_count = 1;
    begin
        switch_beat:
            while switch_count > 0 do
                with new_leader \in NODES do
                    stateboard_leader := new_leader;
                end with;
                switch_count := (switch_count - 1)
            end while;
        end_switch_beat:
            (* Возвращаем исходного лидера репликасета для того,
            что бы "в конце концов" лидером определенно оказался узел №1.
            Без этого невозможно поставить условие конечного восстановления,
            так как в каждом поведении последним был бы неопределенный узел *)
            stateboard_leader := 1;
    end process;

    (* Процесс отражающий за внезапную смерть
    и восстановление инстансов в репликасете *)
    fair process LiveProc \in NODES_MAPPING
    variables
        target_node = (self - NODES_OFFSET);
        beat_count = 1;
    begin
        live_beat:
            while beat_count > 0 do
                either
                (* полностью восстанавливаем узел *)
                    NodeUp(target_node);
                or
                (* полностью отключаем узел *)
                    NodeDown(target_node);
                or
                    if health[target_node] = TRUE then
                    (* переключаем доступность узла *)
                        availability[target_node] := ~availability[target_node]
                    end if;
                end either;
                beat_count := (beat_count - 1);
            end while;

        end_live_beat:
        (* Восстанавливаем все узлы кластера *)
            health[target_node] := TRUE;

    end process;

    (* Основной процесс для каждого узла
    отвечающий за обновление собственного статуса
    согласно информации из внешнего хранилища *)
    fair process FailoverProc \in NODES
    variables
        appointment = stateboard_leader;
    begin
        get_appointment:
        (* гарантируем что ничего не произойдет, если узел отключен *)
            if health[self] = FALSE then
                goto die;
            else    
                if availability[self] = FALSE then
                    leader[self] := FALSE;
                    goto reachless;
                end if;
            end if;
        apply:
        (* применение назначения *)
            if health[self] = FALSE then
                goto die;
            else
                if appointment = self then
                    if availability[last_accepting_leader] = TRUE then
                        await (leader[last_accepting_leader] = FALSE);
                    end if;
                    leader[self] := (appointment = self);
                    last_accepting_leader := self;
                end if;
                goto get_appointment;
            end if;

        die:
            await (health[self] = TRUE);
            goto get_appointment;

        reachless:
            await (availability[self] = TRUE);
            goto get_appointment;
        
    end process;

end algorithm;*)
\* BEGIN TRANSLATION - the hash of the PCal code: PCal-bba36ce5d1dde565e84514fa5a99fe98
VARIABLES health, availability, leader, stateboard_leader, 
          last_accepting_leader, pc

(* define statement *)
AtMostOneMaster == [](\A n1, n2 \in NODES: (n1 /= n2) => ~(leader[n1] = TRUE /\ leader[n2] = TRUE))


EventuallyRecover == <>[](leader[1] = TRUE)

VARIABLES switch_count, target_node, beat_count, appointment

vars == << health, availability, leader, stateboard_leader, 
           last_accepting_leader, pc, switch_count, target_node, beat_count, 
           appointment >>

ProcSet == {GOD} \cup (NODES_MAPPING) \cup (NODES)

Init == (* Global variables *)
        /\ health = [n \in NODES |-> FALSE]
        /\ availability = [n \in NODES |-> FALSE]
        /\ leader = [n \in NODES |-> FALSE]
        /\ stateboard_leader = 1
        /\ last_accepting_leader = 1
        (* Process SwitchProc *)
        /\ switch_count = 1
        (* Process LiveProc *)
        /\ target_node = [self \in NODES_MAPPING |-> (self - NODES_OFFSET)]
        /\ beat_count = [self \in NODES_MAPPING |-> 1]
        (* Process FailoverProc *)
        /\ appointment = [self \in NODES |-> stateboard_leader]
        /\ pc = [self \in ProcSet |-> CASE self = GOD -> "switch_beat"
                                        [] self \in NODES_MAPPING -> "live_beat"
                                        [] self \in NODES -> "get_appointment"]

switch_beat == /\ pc[GOD] = "switch_beat"
               /\ IF switch_count > 0
                     THEN /\ \E new_leader \in NODES:
                               stateboard_leader' = new_leader
                          /\ switch_count' = (switch_count - 1)
                          /\ pc' = [pc EXCEPT ![GOD] = "switch_beat"]
                     ELSE /\ pc' = [pc EXCEPT ![GOD] = "end_switch_beat"]
                          /\ UNCHANGED << stateboard_leader, switch_count >>
               /\ UNCHANGED << health, availability, leader, 
                               last_accepting_leader, target_node, beat_count, 
                               appointment >>

end_switch_beat == /\ pc[GOD] = "end_switch_beat"
                   /\ stateboard_leader' = 1
                   /\ pc' = [pc EXCEPT ![GOD] = "Done"]
                   /\ UNCHANGED << health, availability, leader, 
                                   last_accepting_leader, switch_count, 
                                   target_node, beat_count, appointment >>

SwitchProc == switch_beat \/ end_switch_beat

live_beat(self) == /\ pc[self] = "live_beat"
                   /\ IF beat_count[self] > 0
                         THEN /\ \/ /\ health' = [health EXCEPT ![target_node[self]] = TRUE]
                                    /\ availability' = [availability EXCEPT ![target_node[self]] = TRUE]
                                 \/ /\ health' = [health EXCEPT ![target_node[self]] = FALSE]
                                    /\ availability' = [availability EXCEPT ![target_node[self]] = FALSE]
                                 \/ /\ IF health[target_node[self]] = TRUE
                                          THEN /\ availability' = [availability EXCEPT ![target_node[self]] = ~availability[target_node[self]]]
                                          ELSE /\ TRUE
                                               /\ UNCHANGED availability
                                    /\ UNCHANGED health
                              /\ beat_count' = [beat_count EXCEPT ![self] = (beat_count[self] - 1)]
                              /\ pc' = [pc EXCEPT ![self] = "live_beat"]
                         ELSE /\ pc' = [pc EXCEPT ![self] = "end_live_beat"]
                              /\ UNCHANGED << health, availability, beat_count >>
                   /\ UNCHANGED << leader, stateboard_leader, 
                                   last_accepting_leader, switch_count, 
                                   target_node, appointment >>

end_live_beat(self) == /\ pc[self] = "end_live_beat"
                       /\ health' = [health EXCEPT ![target_node[self]] = TRUE]
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << availability, leader, stateboard_leader, 
                                       last_accepting_leader, switch_count, 
                                       target_node, beat_count, appointment >>

LiveProc(self) == live_beat(self) \/ end_live_beat(self)

get_appointment(self) == /\ pc[self] = "get_appointment"
                         /\ IF health[self] = FALSE
                               THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                                    /\ UNCHANGED leader
                               ELSE /\ IF availability[self] = FALSE
                                          THEN /\ leader' = [leader EXCEPT ![self] = FALSE]
                                               /\ pc' = [pc EXCEPT ![self] = "reachless"]
                                          ELSE /\ pc' = [pc EXCEPT ![self] = "apply"]
                                               /\ UNCHANGED leader
                         /\ UNCHANGED << health, availability, 
                                         stateboard_leader, 
                                         last_accepting_leader, switch_count, 
                                         target_node, beat_count, appointment >>

apply(self) == /\ pc[self] = "apply"
               /\ IF health[self] = FALSE
                     THEN /\ pc' = [pc EXCEPT ![self] = "die"]
                          /\ UNCHANGED << leader, last_accepting_leader >>
                     ELSE /\ IF appointment[self] = self
                                THEN /\ IF availability[last_accepting_leader] = TRUE
                                           THEN /\ (leader[last_accepting_leader] = FALSE)
                                           ELSE /\ TRUE
                                     /\ leader' = [leader EXCEPT ![self] = (appointment[self] = self)]
                                     /\ last_accepting_leader' = self
                                ELSE /\ TRUE
                                     /\ UNCHANGED << leader, 
                                                     last_accepting_leader >>
                          /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
               /\ UNCHANGED << health, availability, stateboard_leader, 
                               switch_count, target_node, beat_count, 
                               appointment >>

die(self) == /\ pc[self] = "die"
             /\ (health[self] = TRUE)
             /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
             /\ UNCHANGED << health, availability, leader, stateboard_leader, 
                             last_accepting_leader, switch_count, target_node, 
                             beat_count, appointment >>

reachless(self) == /\ pc[self] = "reachless"
                   /\ (availability[self] = TRUE)
                   /\ pc' = [pc EXCEPT ![self] = "get_appointment"]
                   /\ UNCHANGED << health, availability, leader, 
                                   stateboard_leader, last_accepting_leader, 
                                   switch_count, target_node, beat_count, 
                                   appointment >>

FailoverProc(self) == get_appointment(self) \/ apply(self) \/ die(self)
                         \/ reachless(self)

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == SwitchProc
           \/ (\E self \in NODES_MAPPING: LiveProc(self))
           \/ (\E self \in NODES: FailoverProc(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ WF_vars(SwitchProc)
        /\ \A self \in NODES_MAPPING : WF_vars(LiveProc(self))
        /\ \A self \in NODES : WF_vars(FailoverProc(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION - the hash of the generated TLA code (remove to silence divergence warnings): TLA-613fca6346c535169bbe7b6c5c561107


===================================================
