------------------------------- MODULE coordinator -------------------------------
EXTENDS TLC, Integers, Sequences
CONSTANT NULL, COORDINATORS

(* --algorithm coordinator
    (* Алгоритм работы координаторов фейловера.
    Это инстансы, которые занимаются тем, что пытаются захватить
    запись своего представления о состоянии кластера(репликасета ) во внешнее хранилище *)

    variables
        lock = [coordinator |-> NULL, expired |-> TRUE],
        leader = NULL,
        (* Временно *)
        tmp_current_leader = NULL
        
    define
        IsLocked == (lock.expired = FALSE)
    end define;

    macro AcquireLock(id)
    (* Захват лока на запись текущего лидера *)
    begin
        if IsLocked = FALSE then
            lock.coordinator := id;
        end if;
    end macro;

    macro SetLeader(coordinator, new_leader)
    (* Запись текущего лидера *)
    begin
        if (lock.coordinator = coordinator) then
            leader := new_leader;
        end if;
    end macro;

    procedure ControlPiece(id)
    variables new_leader = NULL;
    begin
        make_decision:
            (* Решения пока что не имеют иммунитета *)
            new_leader := tmp_current_leader;

        apply:
            SetLeader(id, new_leader); 
        return;
    end procedure;

    process CProc \in COORDINATORS
    begin
        loop_begin:
            skip;
        
        conquer_lock:
            AcquireLock(self);
            (* Если мы не смогли захватить лок, то пробуем заново *)
            if lock.coordinator /= self then
                goto loop_begin;
            end if;    
        
        control:
            while TRUE do
                (* Пока можем контролируем запись *)
                call ControlPiece(self);
                break:
                    if ~IsLocked then
                        goto restart;
                    end if;
            end while;
        restart:
            (* Перезапускаем весь цикл *)
            goto loop_begin;

    end process;

end algorithm;*)

\* BEGIN TRANSLATION
CONSTANT defaultInitValue
VARIABLES lock, leader, tmp_current_leader, pc, stack

(* define statement *)
IsLocked == (lock.expired = FALSE)

VARIABLES id, new_leader

vars == << lock, leader, tmp_current_leader, pc, stack, id, new_leader >>

ProcSet == (COORDINATORS)

Init == (* Global variables *)
        /\ lock = [coordinator |-> NULL, expired |-> TRUE]
        /\ leader = NULL
        /\ tmp_current_leader = NULL
        (* Procedure ControlPiece *)
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        /\ new_leader = [ self \in ProcSet |-> NULL]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "loop_begin"]

make_decision(self) == /\ pc[self] = "make_decision"
                       /\ new_leader' = [new_leader EXCEPT ![self] = tmp_current_leader]
                       /\ pc' = [pc EXCEPT ![self] = "apply"]
                       /\ UNCHANGED << lock, leader, tmp_current_leader, stack, 
                                       id >>

apply(self) == /\ pc[self] = "apply"
               /\ IF (lock.coordinator = id[self])
                     THEN /\ leader' = new_leader[self]
                     ELSE /\ TRUE
                          /\ UNCHANGED leader
               /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
               /\ new_leader' = [new_leader EXCEPT ![self] = Head(stack[self]).new_leader]
               /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
               /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
               /\ UNCHANGED << lock, tmp_current_leader >>

ControlPiece(self) == make_decision(self) \/ apply(self)

loop_begin(self) == /\ pc[self] = "loop_begin"
                    /\ TRUE
                    /\ pc' = [pc EXCEPT ![self] = "conquer_lock"]
                    /\ UNCHANGED << lock, leader, tmp_current_leader, stack, 
                                    id, new_leader >>

conquer_lock(self) == /\ pc[self] = "conquer_lock"
                      /\ IF IsLocked = FALSE
                            THEN /\ lock' = [lock EXCEPT !.coordinator = self]
                            ELSE /\ TRUE
                                 /\ lock' = lock
                      /\ IF lock'.coordinator /= self
                            THEN /\ pc' = [pc EXCEPT ![self] = "loop_begin"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "control"]
                      /\ UNCHANGED << leader, tmp_current_leader, stack, id, 
                                      new_leader >>

control(self) == /\ pc[self] = "control"
                 /\ /\ id' = [id EXCEPT ![self] = self]
                    /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "ControlPiece",
                                                             pc        |->  "break",
                                                             new_leader |->  new_leader[self],
                                                             id        |->  id[self] ] >>
                                                         \o stack[self]]
                 /\ new_leader' = [new_leader EXCEPT ![self] = NULL]
                 /\ pc' = [pc EXCEPT ![self] = "make_decision"]
                 /\ UNCHANGED << lock, leader, tmp_current_leader >>

break(self) == /\ pc[self] = "break"
               /\ IF ~IsLocked
                     THEN /\ pc' = [pc EXCEPT ![self] = "restart"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "control"]
               /\ UNCHANGED << lock, leader, tmp_current_leader, stack, id, 
                               new_leader >>

restart(self) == /\ pc[self] = "restart"
                 /\ pc' = [pc EXCEPT ![self] = "loop_begin"]
                 /\ UNCHANGED << lock, leader, tmp_current_leader, stack, id, 
                                 new_leader >>

CProc(self) == loop_begin(self) \/ conquer_lock(self) \/ control(self)
                  \/ break(self) \/ restart(self)

Next == (\E self \in ProcSet: ControlPiece(self))
           \/ (\E self \in COORDINATORS: CProc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == Init /\ [][Next]_vars

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
===================================================
