------------------------------- MODULE failover -------------------------------
EXTENDS TLC, Naturals
CONSTANT NULL

(* --algorithm failover

    variables
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
        Здесь буду описывать третий сценарий.
        *)
        instances = 1..4,
        (* здесь хранится реальное текущее состояние для каждого инстанса *)
        health = [h \in instances |-> TRUE],
        (* здесь хранится реальная текущая роль для каждого инстанса *)
        leader = [l \in instances |-> FALSE],
        (* выбранный лидер *)
        kingdom_leader = 1

    define
        (* Если существуют как минимум два живых инстанса
        из одного репликасета и они оба являются людерами одновременно,
        то условие инварианта нарушено *)
        AtMostOneMaster == \A m1, m2 \in instances: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE)
   
        (* В конце концов репликасет восстановится - появится лидер *)
        EventuallyClusterRecover == <>(\E m \in instances: leader[m] = TRUE)
    end define;

    (* Процесс отражающий смену лидера внутри репликасета,
    текущее состояние хранится в kingdom masters *)

    process switch = 0
    variables 
    begin
        s1: kingdom_leader := 2;
        s2: kingdom_leader := 3;
        s3: kingdom_leader := 1;
                
    end process;
    
    
    process FailoverProc \in instances
    begin
        init:
            if kingdom_leader = self then
                leader[self] := TRUE;
            end if;
        loop:
            while TRUE do
                died:
                    if health[self] = FALSE then
                        goto continue;
                    end if;

                apply:
                    leader[self] := kingdom_leader = self;
    
                continue:
                    skip;
            end while;
    end process;

end algorithm;*)

\* BEGIN TRANSLATION
VARIABLES instances, health, leader, kingdom_leader, pc

(* define statement *)
AtMostOneMaster == \A m1, m2 \in instances: (m1 /= m2) => ~(leader[m1] = TRUE /\ leader[m2] = TRUE)


EventuallyClusterRecover == <>(\E m \in instances: leader[m] = TRUE)


vars == << instances, health, leader, kingdom_leader, pc >>

ProcSet == {0} \cup (instances)

Init == (* Global variables *)
        /\ instances = 1..4
        /\ health = [h \in instances |-> TRUE]
        /\ leader = [l \in instances |-> FALSE]
        /\ kingdom_leader = 1
        /\ pc = [self \in ProcSet |-> CASE self = 0 -> "s1"
                                        [] self \in instances -> "init"]

s1 == /\ pc[0] = "s1"
      /\ kingdom_leader' = 2
      /\ pc' = [pc EXCEPT ![0] = "s2"]
      /\ UNCHANGED << instances, health, leader >>

s2 == /\ pc[0] = "s2"
      /\ kingdom_leader' = 3
      /\ pc' = [pc EXCEPT ![0] = "s3"]
      /\ UNCHANGED << instances, health, leader >>

s3 == /\ pc[0] = "s3"
      /\ kingdom_leader' = 1
      /\ pc' = [pc EXCEPT ![0] = "Done"]
      /\ UNCHANGED << instances, health, leader >>

switch == s1 \/ s2 \/ s3

init(self) == /\ pc[self] = "init"
              /\ IF kingdom_leader = self
                    THEN /\ leader' = [leader EXCEPT ![self] = TRUE]
                    ELSE /\ TRUE
                         /\ UNCHANGED leader
              /\ pc' = [pc EXCEPT ![self] = "loop"]
              /\ UNCHANGED << instances, health, kingdom_leader >>

loop(self) == /\ pc[self] = "loop"
              /\ pc' = [pc EXCEPT ![self] = "died"]
              /\ UNCHANGED << instances, health, leader, kingdom_leader >>

died(self) == /\ pc[self] = "died"
              /\ IF health[self] = FALSE
                    THEN /\ pc' = [pc EXCEPT ![self] = "continue"]
                    ELSE /\ pc' = [pc EXCEPT ![self] = "apply"]
              /\ UNCHANGED << instances, health, leader, kingdom_leader >>

apply(self) == /\ pc[self] = "apply"
               /\ leader' = [leader EXCEPT ![self] = kingdom_leader = self]
               /\ pc' = [pc EXCEPT ![self] = "continue"]
               /\ UNCHANGED << instances, health, kingdom_leader >>

continue(self) == /\ pc[self] = "continue"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = "loop"]
                  /\ UNCHANGED << instances, health, leader, kingdom_leader >>

FailoverProc(self) == init(self) \/ loop(self) \/ died(self) \/ apply(self)
                         \/ continue(self)

Next == switch
           \/ (\E self \in instances: FailoverProc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
===================================================
