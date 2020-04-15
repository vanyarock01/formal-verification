------------------------------- MODULE lock -------------------------------
EXTENDS Integers, TLC
CONSTANT NULL, INACTIVE, WAIT, ALLOW, COORDINATORS, LOCK_DELAY

(* --algorithm lock

    variables
        lock = [coordinator |-> NULL, session_expiry |-> 0, session_id |-> 0],
        leader = NULL,
        wait_cond = [c \in COORDINATORS |-> INACTIVE],
        (* На старте все считают мастером 1 инстанс *)
        coordinator_leaders = [c \in COORDINATORS |->  1]

    define

    end define;

    macro NotificationBroadcast()
    begin
        with id \in COORDINATORS do
            if wait_cond[id] = WAIT then
                wait_cond[id] := ALLOW;
            end if;
        end with;
    end macro;

    macro SetLeader(coordinator, new_leader)
    begin
        if lock.coordinator = lock.coordinator then
            leader := new_leader;
            NotificationBroadcast(); (* Не должно йилдить! *)
        end if;
    end macro;

    procedure NotificationWait(id)
    begin
        setup:
            wait_cond[id] := WAIT;

        wait:
            await wait_cond[id] /= ALLOW;
            wait_cond[id] := INACTIVE;
    return;
    end procedure;

    procedure Longpoll(id)
    begin
        pre:
            if coordinator_leaders[id] = leader then
                call NotificationWait(id);
            end if;
        set:
            coordinator_leaders[id] := leader;
    return;        
    end procedure;

    procedure AcquireLock(coordinator_id)
    begin
        break:
            if lock.session_expiry == 0
            /\ lock.coordinator /= coordinator_id then
                goto continue;
            end if;

        apply:
            lock.session_expiry := LOCK_DELAY;
            if lock.coordinator /= coordinator_id then
                 s: lock.coordinator := coordinator_id;
            end if;

        continue:
            skip;
    return;
    end procedure;

    fair process CProc \in COORDINATORS
    begin
        try:
            skip;

        call AcquireLock(self);

        conquer_lock:
            if lock.coordinator /= self then
                goto try;
            end if;    

        control:
            (* Контролируем запись *)
            SetLeader(self, coordinator_leaders[self]);

        restart:
            (* Перезапускаем весь цикл *)
            goto try;

    end process;


    end algorithm;
*)
\* BEGIN TRANSLATION
\* Parameter id of procedure NotificationWait at line 35 col 32 changed to id_
CONSTANT defaultInitValue
VARIABLES lock, leader, wait_cond, coordinator_leaders, pc, stack, id_, id, 
          coordinator_id

vars == << lock, leader, wait_cond, coordinator_leaders, pc, stack, id_, id, 
           coordinator_id >>

ProcSet == (COORDINATORS)

Init == (* Global variables *)
        /\ lock = [coordinator |-> NULL, session_expiry |-> 0, session_id |-> 0]
        /\ leader = NULL
        /\ wait_cond = [c \in COORDINATORS |-> INACTIVE]
        /\ coordinator_leaders = [c \in COORDINATORS |->  1]
        (* Procedure NotificationWait *)
        /\ id_ = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure Longpoll *)
        /\ id = [ self \in ProcSet |-> defaultInitValue]
        (* Procedure AcquireLock *)
        /\ coordinator_id = [ self \in ProcSet |-> defaultInitValue]
        /\ stack = [self \in ProcSet |-> << >>]
        /\ pc = [self \in ProcSet |-> "try"]

setup(self) == /\ pc[self] = "setup"
               /\ wait_cond' = [wait_cond EXCEPT ![id_[self]] = WAIT]
               /\ pc' = [pc EXCEPT ![self] = "wait"]
               /\ UNCHANGED << lock, leader, coordinator_leaders, stack, id_, 
                               id, coordinator_id >>

wait(self) == /\ pc[self] = "wait"
              /\ wait_cond[id_[self]] /= ALLOW
              /\ wait_cond' = [wait_cond EXCEPT ![id_[self]] = INACTIVE]
              /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
              /\ id_' = [id_ EXCEPT ![self] = Head(stack[self]).id_]
              /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
              /\ UNCHANGED << lock, leader, coordinator_leaders, id, 
                              coordinator_id >>

NotificationWait(self) == setup(self) \/ wait(self)

pre(self) == /\ pc[self] = "pre"
             /\ IF coordinator_leaders[id[self]] = leader
                   THEN /\ /\ id_' = [id_ EXCEPT ![self] = id[self]]
                           /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "NotificationWait",
                                                                    pc        |->  "set",
                                                                    id_       |->  id_[self] ] >>
                                                                \o stack[self]]
                        /\ pc' = [pc EXCEPT ![self] = "setup"]
                   ELSE /\ pc' = [pc EXCEPT ![self] = "set"]
                        /\ UNCHANGED << stack, id_ >>
             /\ UNCHANGED << lock, leader, wait_cond, coordinator_leaders, id, 
                             coordinator_id >>

set(self) == /\ pc[self] = "set"
             /\ coordinator_leaders' = [coordinator_leaders EXCEPT ![id[self]] = leader]
             /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
             /\ id' = [id EXCEPT ![self] = Head(stack[self]).id]
             /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
             /\ UNCHANGED << lock, leader, wait_cond, id_, coordinator_id >>

Longpoll(self) == pre(self) \/ set(self)

break(self) == /\ pc[self] = "break"
               /\ IF    lock.session_expiry == 0
                     /\ lock.coordinator /= coordinator_id[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "continue"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "apply"]
               /\ UNCHANGED << lock, leader, wait_cond, coordinator_leaders, 
                               stack, id_, id, coordinator_id >>

apply(self) == /\ pc[self] = "apply"
               /\ lock' = [lock EXCEPT !.session_expiry = LOCK_DELAY]
               /\ IF lock'.coordinator /= coordinator_id[self]
                     THEN /\ pc' = [pc EXCEPT ![self] = "s"]
                     ELSE /\ pc' = [pc EXCEPT ![self] = "continue"]
               /\ UNCHANGED << leader, wait_cond, coordinator_leaders, stack, 
                               id_, id, coordinator_id >>

s(self) == /\ pc[self] = "s"
           /\ lock' = [lock EXCEPT !.coordinator = coordinator_id[self]]
           /\ pc' = [pc EXCEPT ![self] = "continue"]
           /\ UNCHANGED << leader, wait_cond, coordinator_leaders, stack, id_, 
                           id, coordinator_id >>

continue(self) == /\ pc[self] = "continue"
                  /\ TRUE
                  /\ pc' = [pc EXCEPT ![self] = Head(stack[self]).pc]
                  /\ coordinator_id' = [coordinator_id EXCEPT ![self] = Head(stack[self]).coordinator_id]
                  /\ stack' = [stack EXCEPT ![self] = Tail(stack[self])]
                  /\ UNCHANGED << lock, leader, wait_cond, coordinator_leaders, 
                                  id_, id >>

AcquireLock(self) == break(self) \/ apply(self) \/ s(self)
                        \/ continue(self)

try(self) == /\ pc[self] = "try"
             /\ TRUE
             /\ /\ coordinator_id' = [coordinator_id EXCEPT ![self] = self]
                /\ stack' = [stack EXCEPT ![self] = << [ procedure |->  "AcquireLock",
                                                         pc        |->  "conquer_lock",
                                                         coordinator_id |->  coordinator_id[self] ] >>
                                                     \o stack[self]]
             /\ pc' = [pc EXCEPT ![self] = "break"]
             /\ UNCHANGED << lock, leader, wait_cond, coordinator_leaders, id_, 
                             id >>

conquer_lock(self) == /\ pc[self] = "conquer_lock"
                      /\ IF lock.coordinator /= self
                            THEN /\ pc' = [pc EXCEPT ![self] = "try"]
                            ELSE /\ pc' = [pc EXCEPT ![self] = "control"]
                      /\ UNCHANGED << lock, leader, wait_cond, 
                                      coordinator_leaders, stack, id_, id, 
                                      coordinator_id >>

control(self) == /\ pc[self] = "control"
                 /\ IF lock.coordinator = lock.coordinator
                       THEN /\ leader' = coordinator_leaders[self]
                            /\ \E id \in COORDINATORS:
                                 IF wait_cond[id[self]] = WAIT
                                    THEN /\ wait_cond' = [wait_cond EXCEPT ![id[self]] = ALLOW]
                                    ELSE /\ TRUE
                                         /\ UNCHANGED wait_cond
                       ELSE /\ TRUE
                            /\ UNCHANGED << leader, wait_cond >>
                 /\ pc' = [pc EXCEPT ![self] = "restart"]
                 /\ UNCHANGED << lock, coordinator_leaders, stack, id_, id, 
                                 coordinator_id >>

restart(self) == /\ pc[self] = "restart"
                 /\ pc' = [pc EXCEPT ![self] = "try"]
                 /\ UNCHANGED << lock, leader, wait_cond, coordinator_leaders, 
                                 stack, id_, id, coordinator_id >>

CProc(self) == try(self) \/ conquer_lock(self) \/ control(self)
                  \/ restart(self)

Next == (\E self \in ProcSet:  \/ NotificationWait(self) \/ Longpoll(self)
                               \/ AcquireLock(self))
           \/ (\E self \in COORDINATORS: CProc(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in COORDINATORS : WF_vars(CProc(self)) /\ WF_vars(AcquireLock(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION
===================================================
