% By Micah Jones
%
% Based loosely on the concept for a nurse scheduling program from the following paper:
% https://www.researchgate.net/publication/221603658_Nurse_Scheduling_using_Constraint_Logic_Programming
%
% For more real world applications of Prolog and CLP in particular, see:
% http://4c.ucc.ie/~hsimonis/ccl2.pdf
%
% Special thanks to Markus Triska for his helpful advice in cleaning up the code here.

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(clpfd)).

:- dynamic employee/1.
:- dynamic employee_max_shifts/2.
:- dynamic employee_skill/2.
:- dynamic task_skills/2.
:- dynamic employee_unavailable/2.
:- dynamic task/2.
:- dynamic employee_assigned/2.

employee(micah).
employee(jonathan).
employee(blake).

employee_max_shifts(micah,10).
employee_max_shifts(jonathan,12).
employee_max_shifts(blake,10).

employee_skill(micah,programming).
employee_skill(micah,writing).
employee_skill(micah,speaking).
employee_skill(micah,nunchucks).
employee_skill(jonathan,programming).
employee_skill(jonathan,babysitting).
employee_skill(jonathan,writing).
employee_skill(blake,programming).
employee_skill(blake,speaking).

task_skills(documentation,[programming,writing,babysitting]).
task_skills(web_design,[programming]).
task_skills(server_programming,[programming]).
task_skills(presentation,[speaking]).

employee_unavailable(micah,shift(friday,1)).
employee_unavailable(micah,shift(friday,2)).
employee_unavailable(micah,shift(saturday,1)).
employee_unavailable(micah,shift(saturday,2)).

shifts([
    shift(monday,1),shift(monday,2),
    shift(tuesday,1),shift(tuesday,2),
    shift(wednesday,1),shift(wednesday,2),
    shift(thursday,1),shift(thursday,2),
    shift(friday,1),shift(friday,2),
    shift(saturday,1),shift(saturday,2),
    shift(sunday,1),shift(sunday,2)]).


% tasks to assign
task(documentation,shift(saturday,1)).
%task(documentation,shift(monday,2)).

%task(web_design,shift(monday,1)).
%task(web_design,shift(monday,2)).
%task(web_design,shift(tuesday,1)).
%task(web_design,shift(tuesday,2)).
%task(web_design,shift(wednesday,1)).
%task(web_design,shift(wednesday,2)).
%task(web_design,shift(thursday,1)).
%task(web_design,shift(thursday,2)).
task(web_design,shift(saturday,1)).
%task(web_design,shift(saturday,2)).

%task(server_programming,shift(monday,1)).
%task(server_programming,shift(monday,2)).
%task(server_programming,shift(tuesday,1)).
%task(server_programming,shift(tuesday,2)).
%task(server_programming,shift(wednesday,1)).
%task(server_programming,shift(wednesday,2)).
%task(server_programming,shift(thursday,1)).
%task(server_programming,shift(thursday,2)).
%task(server_programming,shift(friday,1)).
%task(server_programming,shift(friday,2)).

task(presentation,shift(friday,1)).


%employee_assigned(micah,task(web_design,shift(monday,1))).
%employee_assigned(jonathan,task(web_design,shift(monday,2))).
%employee_assigned(micah,task(web_design,shift(tuesday,1))).
%employee_assigned(micah,task(web_design,shift(tuesday,2))).
%employee_assigned(blake,task(server_programming,shift(monday,1))).
%employee_assigned(blake,task(server_programming,shift(monday,2))).


% get_employees(-Employees)
get_employees(Employees) :-
    findall(employee(E),employee(E),Employees).
% get_tasks(-Tasks)
get_tasks(Tasks) :-
    findall(task(TName,TShift),task(TName,TShift),Tasks).

% create_assoc_list(+Employees,+Tasks,-Assoc)
% Find all combinations of pairs and assign each a variable to track
create_assoc_list(Es,Ts,Assoc) :-
    empty_assoc(EmptyAssoc),
    findall(assign(E,T),(member(E,Es),member(T,Ts)),AssignmentPairs),
    build_assoc_list(EmptyAssoc,AssignmentPairs,Assoc).

% build_assoc_list(+AssocAcc,+Pairs,-Assoc)
build_assoc_list(Assoc,[],Assoc).
build_assoc_list(AssocAcc,[Pair|Pairs],Assoc) :-
    put_assoc(Pair,AssocAcc,_Var,AssocAcc2),
    build_assoc_list(AssocAcc2,Pairs,Assoc).
    
% assoc_keys_vars(+Assoc,+Keys,-Vars)
%
% Retrieves all Vars from Assoc corresponding to Keys.
% (Note: At first it seems we could use a fancy findall in place of this, but findall
% will replace the Vars with new variable references, which ruins our map.)
assoc_keys_vars(Assoc, Keys, Vars) :-
        maplist(assoc_key_var(Assoc), Keys, Vars).
assoc_key_var(Assoc, Key, Var) :- get_assoc(Key, Assoc, Var).

% list_or(+Exprs,-Disjunction)
list_or([L|Ls], Or) :- foldl(disjunction_, Ls, L, Or).
disjunction_(A, B, B#\/A).


% schedule(-Schedule)
%
% Uses clp(fd) to generate a schedule of assignments, as a list of assign(Employee,Task)
% elements. Adheres to the following rules:
% (1) Every task must have at least one employee assigned to it.
% (2) No employee may be assigned to multiple tasks in the same shift.
% (3) No employee may be assigned to more than their maximum number of shifts.
% (4) No employee may be assigned to a task during a shift in which they are unavailable.
% (5) No employee may be assigned to a task for which they lack necessary skills.
% (6) Any pre-existing assignments (employee_assigned) must still hold.
schedule(Schedule) :-
    get_employees(Es),
    get_tasks(Ts),
    create_assoc_list(Es,Ts,Assoc),
    assoc_to_keys(Assoc,AssocKeys),
    assoc_to_values(Assoc,AssocValues),
    constraints(Assoc,Es,Ts),
    
    label(AssocValues),
    
   % The following commented lines are useful for writing out the solution in an intuitive format
    writeln('Assoc = '),
    findall(_,(
            member(Key,AssocKeys),
            get_assoc(Key,Assoc,Val),
            format('(~w,~w)~n',[Key,Val])
        ),_),
    
    findall(AssocKey,(member(AssocKey,AssocKeys),get_assoc(AssocKey,Assoc,1)),Assignments),
    Schedule = Assignments.
    
    
% constraints(+Assoc,+Employees,+Tasks)
constraints(Assoc,Es,Ts) :-
    core_constraints(Assoc,Es,Ts),
    simul_constraints(Assoc,Es,Ts),
    max_shifts_constraints(Assoc,Es,Ts),
    unavailable_constraints(Assoc,Es,Ts),
    skills_constraints(Assoc,Es,Ts),
    assigned_constraints(Assoc).
    
% core_constraints(+Assoc,+Employees,+Tasks)
%
% Builds the main conjunctive sequence of the form:
% (A_e(0),t(0) \/ A_e(1),t(0) \/ ...) /\ (A_e(0),t(1) \/ A_e(1),t(1) \/ ...) /\ ...
core_constraints(Assoc,Es,Ts) :-
    maplist(core_constraints_disj(Assoc,Es),Ts).

% core_constraints_disj(+Assoc,+Employees,+Task)
% Helper for core_constraints, builds a disjunction of sub-expressions, such that
% at least one employee must be assigned to Task
core_constraints_disj(Assoc,Es,T) :-
    findall(assign(E,T),member(E,Es),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    list_or(Vars,Disj),
    Disj.


% simul_constraints(+Assoc,+Employees,+Tasks)
%
% Builds a constraint expression to prevent one person from being assigned to multiple
% tasks at the same time. Of the form:
% (A_e(0),t(n1) + A_e(0),t(n2) + ... #=< 1) /\ (A_e(1),t(n1) + A_e(1),t(n2) + ... #=< 1)
% where n1,n2,etc. are indices of tasks that occur at the same time.
simul_constraints(Assoc,Es,Ts) :-
    shifts(Shifts),
    findall(employee_shift(E,Shift),(member(E,Es),member(Shift,Shifts)),EmployeeShifts),
    maplist(simul_constraints_subexpr(Assoc,Ts),EmployeeShifts).
    
simul_constraints_subexpr(Assoc,Ts,employee_shift(E,Shift)) :-
    findall(task(TName,Shift),member(task(TName,Shift),Ts),ShiftTs),
    findall(assign(E,T),member(T,ShiftTs),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    sum(Vars,#=<,1).


% max_shifts_constraints(+Assoc,+Employees,+Tasks)
%
% Builds a constraint expression that prevents employees from being assigned too many
% shifts. Of the form:
% (A_e(0),t(0) + A_e(0),t(1) + ... #=< M_e(0)) /\ (A_e(1),t(0) + A_e(1),t(1) + ... #=< M_e(1)) /\ ...
% where M_e(n) is the max number of shifts for employee n.
max_shifts_constraints(Assoc,Es,Ts) :-
    maplist(max_shifts_subexpr(Assoc,Ts),Es).

max_shifts_subexpr(Assoc,Ts,E) :-
    E = employee(EName),
    employee_max_shifts(EName,MaxShifts),
    findall(assign(E,T),member(T,Ts),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    sum(Vars,#=<,MaxShifts).


% unavailable_constraints(+Assoc,+Employees,+Tasks)
%
% For every shift for which an employee e(n) is unavailable, add a constraint of the form
% A_e(n),t(x) = 0 for every t(x) that occurs during that shift. Note that 0 is equivalent
% to False in clp(fd).
unavailable_constraints(Assoc,Es,Ts) :-
    findall(assign(E,T),(
            member(E,Es),
            E = employee(EName),
            employee_unavailable(EName,Shift),
            member(T,Ts),
            T = task(_TName,Shift)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(#=(0),Vars).


% skills_constraints(+Assoc,+Employees,+Tasks)
%
% For every task t(m) for which an employee e(n) lacks sufficient skills, add a
% constraint of the form A_e(n),t(m) = 0.
skills_constraints(Assoc,Es,Ts) :-
    findall(assign(E,T),(
            member(T,Ts),
            T = task(TName,_TShift),
            task_skills(TName,TSkills),
            member(E,Es),
            \+employee_has_skills(E,TSkills)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(#=(0),Vars).
                    

% employee_has_skills(+Employee,+Skills)
%
% Fails if Employee does not possess all Skills.
employee_has_skills(employee(EName),Skills) :-
    findall(ESkill,employee_skill(EName,ESkill),ESkills),
    subset(Skills,ESkills).
    

% assigned_constraints(+Assoc)
%
% For every task t(m) to which an employee e(n) is already assigned, add a constraint
% of the form A_e(n),t(m) = 1 to force the assignment into the schedule. Note that
% we execute this constraint inline here instead of collecting it into a Constraint list.
assigned_constraints(Assoc) :-
    findall(assign(E,T),(
            employee_assigned(EName,T),
            E = employee(EName)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(#=(1),Vars).
        
        