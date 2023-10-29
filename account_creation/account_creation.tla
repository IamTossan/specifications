---- MODULE account_creation ----
EXTENDS TLC, Sequences, Integers, FiniteSets
CONSTANTS
    NULL,
    new_clients,
    account_managers

(*--algorithm account_creation
variable
    tasks = new_clients,
    requests = <<>>,
    error_logs = <<>>,
    email_sent = <<>>;

define
end define;

fair process account_manager \in account_managers
begin RequestAccountCreation:
    while tasks /= {} do
        with new_client = CHOOSE t \in tasks: TRUE do
            tasks := tasks \ {new_client};
            requests := requests \o <<new_client>>;
        end with;
    end while;
end process;

fair process server = "server"
variables all_tasks_processed = FALSE;
begin HandleRequestAccountCreation:
    while ~all_tasks_processed do
        await requests /= <<>>;
        with current_request = Head(requests) do
            either
                \* Failed to create account
                error_logs := error_logs \o <<current_request>>
            or
                \* Create account
                email_sent := email_sent \o <<current_request>>
            end either;
            requests := Tail(requests);
        end with;
        if tasks = {} /\ requests = <<>> then
            all_tasks_processed := TRUE
        end if;
    end while;
end process;

end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "4d071059" /\ chksum(tla) = "3f7b80ca")
VARIABLES tasks, requests, error_logs, email_sent, pc, all_tasks_processed

vars == << tasks, requests, error_logs, email_sent, pc, all_tasks_processed
        >>

ProcSet == (account_managers) \cup {"server"}

Init == (* Global variables *)
        /\ tasks = new_clients
        /\ requests = <<>>
        /\ error_logs = <<>>
        /\ email_sent = <<>>
        (* Process server *)
        /\ all_tasks_processed = FALSE
        /\ pc = [self \in ProcSet |-> CASE self \in account_managers -> "RequestAccountCreation"
                                        [] self = "server" -> "HandleRequestAccountCreation"]

RequestAccountCreation(self) == /\ pc[self] = "RequestAccountCreation"
                                /\ IF tasks /= {}
                                      THEN /\ LET new_client == CHOOSE t \in tasks: TRUE IN
                                                /\ tasks' = tasks \ {new_client}
                                                /\ requests' = requests \o <<new_client>>
                                           /\ pc' = [pc EXCEPT ![self] = "RequestAccountCreation"]
                                      ELSE /\ pc' = [pc EXCEPT ![self] = "Done"]
                                           /\ UNCHANGED << tasks, requests >>
                                /\ UNCHANGED << error_logs, email_sent, 
                                                all_tasks_processed >>

account_manager(self) == RequestAccountCreation(self)

HandleRequestAccountCreation == /\ pc["server"] = "HandleRequestAccountCreation"
                                /\ IF ~all_tasks_processed
                                      THEN /\ requests /= <<>>
                                           /\ LET current_request == Head(requests) IN
                                                /\ \/ /\ error_logs' = error_logs \o <<current_request>>
                                                      /\ UNCHANGED email_sent
                                                   \/ /\ email_sent' = email_sent \o <<current_request>>
                                                      /\ UNCHANGED error_logs
                                                /\ requests' = Tail(requests)
                                           /\ IF tasks = {} /\ requests' = <<>>
                                                 THEN /\ all_tasks_processed' = TRUE
                                                 ELSE /\ TRUE
                                                      /\ UNCHANGED all_tasks_processed
                                           /\ pc' = [pc EXCEPT !["server"] = "HandleRequestAccountCreation"]
                                      ELSE /\ pc' = [pc EXCEPT !["server"] = "Done"]
                                           /\ UNCHANGED << requests, 
                                                           error_logs, 
                                                           email_sent, 
                                                           all_tasks_processed >>
                                /\ tasks' = tasks

server == HandleRequestAccountCreation

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == /\ \A self \in ProcSet: pc[self] = "Done"
               /\ UNCHANGED vars

Next == server
           \/ (\E self \in account_managers: account_manager(self))
           \/ Terminating

Spec == /\ Init /\ [][Next]_vars
        /\ \A self \in account_managers : WF_vars(account_manager(self))
        /\ WF_vars(server)

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION 

Liveness ==
    LET
        xs == error_logs \o email_sent 
    IN
        /\ <>[](tasks = {})
        /\ <>[](Len(xs) = Cardinality(new_clients))
        /\ <>[](\A i \in 1..Len(xs): xs[i] \in new_clients) 
====
