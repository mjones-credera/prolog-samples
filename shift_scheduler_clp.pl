% By Micah Jones
%
% Based loosely on the concept for a nurse scheduling program from the following paper:
% https://www.aaai.org/Papers/IAAI/1999/IAAI99-118.pdf
%
% For more real world applications of Prolog and CLP in particular, see:
% http://4c.ucc.ie/~hsimonis/ccl2.pdf
%
% Special thanks to Markus Triska for his helpful advice in cleaning up the code here.

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(clpfd)).

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

task_skills(documentation,[programming,writing]).
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
task(documentation,shift(monday,2)).

task(web_design,shift(monday,1)).
task(web_design,shift(monday,2)).
task(web_design,shift(tuesday,1)).
task(web_design,shift(tuesday,2)).
task(web_design,shift(wednesday,1)).
task(web_design,shift(wednesday,2)).
task(web_design,shift(thursday,1)).
task(web_design,shift(thursday,2)).
task(web_design,shift(saturday,1)).
task(web_design,shift(saturday,2)).

task(server_programming,shift(monday,1)).
task(server_programming,shift(monday,2)).
task(server_programming,shift(tuesday,1)).
task(server_programming,shift(tuesday,2)).
task(server_programming,shift(wednesday,1)).
task(server_programming,shift(wednesday,2)).
task(server_programming,shift(thursday,1)).
task(server_programming,shift(thursday,2)).
task(server_programming,shift(friday,1)).
task(server_programming,shift(friday,2)).

task(presentation,shift(friday,1)).


employee_assigned(micah,task(web_design,shift(monday,1))).
employee_assigned(jonathan,task(web_design,shift(monday,2))).
employee_assigned(micah,task(web_design,shift(tuesday,1))).
employee_assigned(micah,task(web_design,shift(tuesday,2))).
employee_assigned(blake,task(server_programming,shift(monday,1))).
employee_assigned(blake,task(server_programming,shift(monday,2))).


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

% list_to_and(+Exprs,-Conjunction)
% list_to_or(+Exprs,-Disjunction)
% list_to_sum(+Exprs,-Sum)
list_to_and([], 1).
list_to_and([L|Ls], And) :- foldl(conjunction_, Ls, L, And).
list_to_or([], 1).
list_to_or([L|Ls], Or) :- foldl(disjunction_, Ls, L, Or).
list_to_sum([],0).
list_to_sum([L|Ls], Sum) :- foldl(sum_, Ls, L, Sum).

conjunction_(A, B, B#/\A).
disjunction_(A, B, B#\/A).
sum_(A,B,B+A).


% schedule(-Schedule)
%
% Uses clp(fd) to generate a schedule of assignments, as a list of assign(Employee,Task)
% elements. Adheres to the following rules:
% (1) Every task must have an employee assigned to it.
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
    build_constraints(Assoc,Es,Ts,Constraints),
    
    Constraints,
    label(AssocValues),
    
    findall(AssocKey,(member(AssocKey,AssocKeys),get_assoc(AssocKey,Assoc,1)),Assignments),
    Schedule = Assignments.
    
    
% build_constraints(+Assoc,+Employees,+Tasks,-Constraints)
build_constraints(Assoc,Es,Ts,Constraints) :-
    core_constraints(Assoc,Es,Ts,CoreConstraints),
    simul_constraints(Assoc,Es,Ts,SimulConstraints),
    max_shifts_constraints(Assoc,Es,Ts,MaxShiftsConstraints),
    unavailable_constraints(Assoc,Es,Ts,UnavailableConstraints),
    skills_constraints(Assoc,Es,Ts,SkillsConstraints),
    assigned_constraints(Assoc,AssignedConstraints),
    list_to_and(
        [CoreConstraints,SimulConstraints,MaxShiftsConstraints,
         UnavailableConstraints,SkillsConstraints,AssignedConstraints],
        Constraints).
    
% core_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Builds the main conjunctive sequence of the form:
% (A_e(0),t(0) \/ A_e(1),t(0) \/ ...) /\ (A_e(0),t(1) \/ A_e(1),t(1) \/ ...) /\ ...
core_constraints(Assoc,Es,Ts,Constraints) :-
    maplist(core_constraints_disj(Assoc,Es),Ts,Disjs),
    list_to_and(Disjs,Constraints).

% core_constraints_disj(+Assoc,+Employees,+Task,-Disjunction)
% Helper for core_constraints, builds a disjunction of sub-expressions, such that
% at least one employee must be assigned to Task
core_constraints_disj(Assoc,Es,T,Disj) :-
    findall(assign(E,T),member(E,Es),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    list_to_or(Vars,Disj).


% simul_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Builds a constraint expression to prevent one person from being assigned to multiple
% tasks at the same time. Of the form:
% (A_e(0),t(n1) + A_e(0),t(n2) + ... #=< 1) /\ (A_e(1),t(n1) + A_e(1),t(n2) + ... #=< 1)
% where n1,n2,etc. are indices of tasks that occur at the same time.
simul_constraints(Assoc,Es,Ts,Constraints) :-
    shifts(Shifts),
    findall(employee_shift(E,Shift),(member(E,Es),member(Shift,Shifts)),EmployeeShifts),
    maplist(simul_constraints_subexpr(Assoc,Ts),EmployeeShifts,SubExprs),
    list_to_and(SubExprs,Constraints).
    
simul_constraints_subexpr(Assoc,Ts,employee_shift(E,Shift),(SumExpr #=< 1)) :-
    findall(task(TName,Shift),member(task(TName,Shift),Ts),ShiftTs),
    findall(assign(E,T),member(T,ShiftTs),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    list_to_sum(Vars,SumExpr).


% max_shifts_constraints(+Assoc,+Employees,+Tasks,-MaxShiftsConstraints)
%
% Builds a constraint expression that prevents employees from being assigned too many
% shifts. Of the form:
% (A_e(0),t(0) + A_e(0),t(1) + ... #=< M_e(0)) /\ (A_e(1),t(0) + A_e(1),t(1) + ... #=< M_e(1)) /\ ...
% where M_e(n) is the max number of shifts for employee n.
max_shifts_constraints(Assoc,Es,Ts,MaxShiftsConstraints) :-
    maplist(max_shifts_subexpr(Assoc,Ts),Es,SubExprs),
    list_to_and(SubExprs,MaxShiftsConstraints).

max_shifts_subexpr(Assoc,Ts,E,(SumExpr #=< MaxShifts)) :-
    E = employee(EName),
    employee_max_shifts(EName,MaxShifts),
    findall(assign(E,T),member(T,Ts),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    list_to_sum(Vars,SumExpr).


% unavailable_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% For every shift for which an employee e(n) is unavailable, add a constraint of the form
% A_e(n),t(x) = 0 for every t(x) that occurs during that shift. Note that 0 is equivalent
% to False in clp(fd).
unavailable_constraints(Assoc,Es,Ts,Constraints) :-
    findall(assign(E,T),(
            member(E,Es),
            E = employee(EName),
            employee_unavailable(EName,Shift),
            member(T,Ts),
            T = task(_TName,Shift)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(var_is_false,Vars,FalseVars),
    list_to_and(FalseVars,Constraints).


% skills_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% For every task t(m) for which an employee e(n) lacks sufficient skills, add a
% constraint of the form A_e(n),t(m) = 0.
skills_constraints(Assoc,Es,Ts,Constraints) :-
    findall(assign(E,T),(
            member(T,Ts),
            T = task(TName,_TShift),
            task_skills(TName,TSkills),
            member(E,Es),
            \+employee_has_skills(E,TSkills)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(var_is_false,Vars,FalseVars),
    list_to_and(FalseVars,Constraints).
                    

% employee_has_skills(+Employee,+Skills)
%
% Fails if Employee does not possess all Skills.
employee_has_skills(employee(EName),Skills) :-
    findall(ESkill,employee_skill(EName,ESkill),ESkills),
    subset(Skills,ESkills).
    

% assigned_constraints(+Assoc,-Constraints)
%
% For every task t(m) to which an employee e(n) is already assigned, add a constraint
% of the form A_e(n),t(m) = 1 to force the assignment into the schedule.
assigned_constraints(Assoc,Constraints) :-
    findall(assign(E,T),(
            employee_assigned(EName,T),
            E = employee(EName)
        ),Keys),
    assoc_keys_vars(Assoc,Keys,Vars),
    maplist(var_is_true,Vars,TrueVars),
    list_to_and(TrueVars,Constraints).
        
        
% var_is_false(+Var,-Expr)
var_is_false(Var,Var#=0).
var_is_true(Var,Var#=1).
        