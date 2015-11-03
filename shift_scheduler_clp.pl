:- use_module(library(clpfd)).

employee(micah).
employee(jonathan).
employee(blake).

max_shifts(micah,10).
max_shifts(jonathan,12).
max_shifts(blake,10).

skill(micah,programming).
skill(micah,writing).
skill(micah,speaking).
skill(micah,nunchucks).
skill(jonathan,programming).
skill(jonathan,babysitting).
skill(jonathan,writing).
skill(blake,programming).
skill(blake,speaking).

task_skills(documentation,[programming,writing]).
task_skills(web_design,[programming]).
task_skills(server_programming,[programming]).
task_skills(presentation,[speaking]).

unavailable(micah,shift(friday,1)).
unavailable(micah,shift(friday,2)).
unavailable(micah,shift(saturday,1)).
unavailable(micah,shift(saturday,2)).

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
    
% get_assoc_vars(+Assoc,+Keys,-Vars)
%
% Retrieves all Vars from Assoc corresponding to Keys.
% (Note: At first it seems we could use a fancy findall in place of this, but findall
% will replace the Vars with new variable references, which ruins our map.)
get_assoc_vars(Assoc,Keys,Vars) :-
    get_assoc_vars(Assoc,Keys,[],Vars).
    
get_assoc_vars(_,[],Vars,Vars).
get_assoc_vars(Assoc,[Key|Keys],VarsAcc,Vars) :-
    get_assoc(Key,Assoc,Var),
    append(VarsAcc,[Var],VarsAcc2),
    get_assoc_vars(Assoc,Keys,VarsAcc2,Vars).
    
% convert_list_to_and(+Exprs,-Conjunction) :-
convert_list_to_and([],1).
convert_list_to_and([Expr],Expr).
convert_list_to_and([Expr|Exprs],Conjunction) :-
    Exprs \= [],
    convert_list_to_and(Exprs,Conjunction2),
    Conjunction = #/\(Expr,Conjunction2).

% convert_list_to_or(+Exprs,-Disjunction) :-
convert_list_to_or([],1).
convert_list_to_or([Expr],Expr).
convert_list_to_or([Expr|Exprs],Disjunction) :-
    Exprs \= [],
    convert_list_to_or(Exprs,Disjunction2),
    Disjunction = #\/(Expr,Disjunction2).

% convert_list_to_chained_op(+Op,+Exprs,-Chain)
convert_list_to_chained_op(_,[],0).
convert_list_to_chained_op(_,[Expr],Expr).
convert_list_to_chained_op(Op,[Expr|Exprs],Chain) :-
    Exprs \= [],
    convert_list_to_chained_op(Op,Exprs,Chain2),
    Chain =.. [Op,Expr,Chain2].


% schedule(-Schedule)
schedule(Schedule) :-
    get_employees(Es),
    get_tasks(Ts),
    create_assoc_list(Es,Ts,Assoc),
    assoc_to_keys(Assoc,AssocKeys),
    assoc_to_values(Assoc,AssocValues),
    build_constraints(Assoc,Es,Ts,Constraints),
    
    Constraints,
    label(AssocValues),
    
    write('Constraints = '),writeln(Constraints),writeln(''),
    writeln('Assoc = '),
    findall(_,(
            member(Key,AssocKeys),
            get_assoc(Key,Assoc,Val),
            format('(~w,~w)~n',[Key,Val])
        ),_),
    
    findall(AssocKey,(member(AssocKey,AssocKeys),get_assoc(AssocKey,Assoc,1)),Assignments),
    Schedule = Assignments.
    
    
% build_constraints(+Assoc,+Employees,+Tasks,-Constraints)
build_constraints(Assoc,Es,Ts,Constraints) :-
    build_core_constraints(Assoc,Es,Ts,CoreConstraints),
    build_simultaneous_constraints(Assoc,Es,Ts,SimultaneousConstraints),
    build_max_shifts_constraints(Assoc,Es,Ts,MaxShiftsConstraints),
    build_unavailable_constraints(Assoc,Es,Ts,UnavailableConstraints),
    build_skills_constraints(Assoc,Es,Ts,SkillsConstraints),
    convert_list_to_and(
        [CoreConstraints,SimultaneousConstraints,MaxShiftsConstraints,UnavailableConstraints,SkillsConstraints],
        Constraints).
    
% build_core_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Builds the main conjunctive sequence of the form:
% (A_e(0),t(0) + A_e(1),t(0) + ...) * (A_e(0),t(1) + A_e(1),t(1) + ...) * ...
build_core_constraints(Assoc,Es,Ts,Constraints) :-
    build_core_constraints_task(Assoc,Es,Ts,[],Constraints).

% build_core_constraints_task(+Assoc,+Employees,+Tasks,+ConstraintsAcc,-Constraints)
% Helper for build_core_constraints, builds a conjunction of sub-expressions, each of
% which requires at least one employee to be assigned to a given task.
build_core_constraints_task(_,_,[],Constraints,AndConstraints) :-
    convert_list_to_and(Constraints,AndConstraints).
build_core_constraints_task(Assoc,Es,[T|Ts],ConstraintsAcc,Constraints) :-
    build_core_constraints_employee(Assoc,Es,T,[],TaskConstraints),
    append(ConstraintsAcc,[TaskConstraints],ConstraintsAcc2),
    build_core_constraints_task(Assoc,Es,Ts,ConstraintsAcc2,Constraints).

% build_core_constraints_employee(+Assoc,+Employees,+Task,+ConstraintsAcc,-Constraints)
% Helper for build_core_constraints_task, builds a disjunctive sequence of employees per task
build_core_constraints_employee(_,[],_,Constraints,OrConstraints) :-
    convert_list_to_or(Constraints,OrConstraints).
build_core_constraints_employee(Assoc,[E|Es],T,ConstraintsAcc,Constraints) :-
    get_assoc(assign(E,T),Assoc,Var),
    append(ConstraintsAcc,[Var],ConstraintsAcc2),
    build_core_constraints_employee(Assoc,Es,T,ConstraintsAcc2,Constraints).
    

% build_simultaneous_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Builds a constraint expression to prevent one person from being assigned to multiple
% tasks at the same time. Of the form:
% (A_e(0),t(n1) + A_e(0),t(n2) + ... #=< 1) * (A_e(1),t(n1) + A_e(1),t(n2) + ... #=< 1)
% where n1,n2,etc. are indices of tasks that occur at the same time.
build_simultaneous_constraints(Assoc,Es,Ts,Constraints) :-
    shifts(Shifts),
    % TasksGroupedByShift is of the form [[t(a1),t(a2),...],[t(b1),t(b2),...],...] where a,b,etc. are shifts
    findall(ShiftTasks,(
            member(Shift,Shifts),
            findall(task(TaskName,Shift),member(task(TaskName,Shift),Ts),ShiftTasks)
        ),TasksGroupedByShift),
    build_simultaneous_constraints_employee(Assoc,Es,TasksGroupedByShift,[],Constraints).

% build_simultaneous_constraints_employee(+Assoc,+Employees,+TasksGroupedByShift,+ConstraintsAcc,-Constraints)
build_simultaneous_constraints_employee(_,[],_,Constraints,AndConstraints) :-
    convert_list_to_and(Constraints,AndConstraints).
build_simultaneous_constraints_employee(Assoc,[E|Es],TasksGroupedByShift,ConstraintsAcc,Constraints) :-
    build_simultaneous_constraints_shift(Assoc,E,TasksGroupedByShift,[],EmployeeConstraints),
    append(ConstraintsAcc,EmployeeConstraints,ConstraintsAcc2),
    build_simultaneous_constraints_employee(Assoc,Es,TasksGroupedByShift,ConstraintsAcc2,Constraints).

% build_simultaneous_constraints_shift(+Assoc,+Employee,+TasksGroupedByShift,+ConstraintsAcc,-Constraints)
build_simultaneous_constraints_shift(_,_,[],Constraints,Constraints).
build_simultaneous_constraints_shift(Assoc,E,[Ts|TasksGroupedByShift],ConstraintsAcc,Constraints) :-
    findall(assign(E,T),member(T,Ts),Keys),
    get_assoc_vars(Assoc,Keys,Vars),
    convert_list_to_chained_op('+',Vars,SumExpr),
    append(ConstraintsAcc,[SumExpr #=< 1],ConstraintsAcc2),
    build_simultaneous_constraints_shift(Assoc,E,TasksGroupedByShift,ConstraintsAcc2,Constraints).
    

% build_max_shifts_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Builds a constraint expression that prevents employees from being assigned too many shifts.
build_max_shifts_constraints(Assoc,Es,Ts,Constraints) :-
    build_max_shifts_constraints_employee(Assoc,Es,Ts,[],Constraints).

build_max_shifts_constraints_employee(_,[],_,Constraints,AndConstraints) :-
    convert_list_to_and(Constraints,AndConstraints).
build_max_shifts_constraints_employee(Assoc,[E|Es],Ts,ConstraintsAcc,Constraints) :-
    E = employee(EmployeeName),
    max_shifts(EmployeeName,MaxShifts),
    findall(assign(E,T),member(T,Ts),Keys),
    get_assoc_vars(Assoc,Keys,Vars),
    convert_list_to_chained_op('+',Vars,SumExpr),
    append(ConstraintsAcc,[SumExpr #=< MaxShifts],ConstraintsAcc2),
    build_max_shifts_constraints_employee(Assoc,Es,Ts,ConstraintsAcc2,Constraints).


% build_unavailable_constraints(+Assoc,+Employees,+Tasks,-Constraints)
build_unavailable_constraints(Assoc,Es,Ts,Constraints) :-
    build_unavailable_constraints_employees(Assoc,Es,Ts,[],Constraints).
    
% build_unavailable_constraints_employees(+Assoc,+Employees,+Tasks,+ConstraintsAcc,-Constraints)
build_unavailable_constraints_employees(_,[],_,Constraints,AndConstraints) :-
    convert_list_to_and(Constraints,AndConstraints).
build_unavailable_constraints_employees(Assoc,[E|Es],Ts,ConstraintsAcc,Constraints) :-
    E = employee(EmployeeName),
    findall(Shift,unavailable(EmployeeName,Shift),UnavailableShifts),
    findall(assign(E,T),(
            member(UnavailableShift,UnavailableShifts),
            member(task(TaskName,UnavailableShift),Ts),
            T = task(TaskName,UnavailableShift)
        ),Keys),
    get_assoc_vars(Assoc,Keys,Vars),
    falsify_vars(Vars,FalsifiedList),
    append(ConstraintsAcc,FalsifiedList,ConstraintsAcc2),
    build_unavailable_constraints_employees(Assoc,Es,Ts,ConstraintsAcc2,Constraints).
    

% build_skills_constraints(+Assoc,+Employees,+Tasks,-Constraints)
%
% Exclude all tasks for which the employee lacks the necessary skills.
build_skills_constraints(Assoc,Es,Ts,Constraints) :-
    build_skills_constraints_employees(Assoc,Es,Ts,[],Constraints).
    
% build_skills_constraints_employees(+Assoc,+Employees,+Tasks,+ConstraintsAcc,-Constraints)
build_skills_constraints_employees(_,[],_,Constraints,AndConstraints) :-
    convert_list_to_and(Constraints,AndConstraints).
build_skills_constraints_employees(Assoc,[E|Es],Ts,ConstraintsAcc,Constraints) :-
    E = employee(EmployeeName),
    findall(assign(E,T),(
            member(task(TaskName,TaskShift),Ts),
            task_skills(TaskName,TaskSkills),
            \+has_skills(EmployeeName,TaskSkills),
            T = task(TaskName,TaskShift)
        ),Keys),
    get_assoc_vars(Assoc,Keys,Vars),
    falsify_vars(Vars,FalsifiedList),
    append(ConstraintsAcc,FalsifiedList,ConstraintsAcc2),
    build_skills_constraints_employees(Assoc,Es,Ts,ConstraintsAcc2,Constraints).
    

falsify_vars(Vars,FalsifiedList) :- falsify_vars(Vars,[],FalsifiedList).

falsify_vars([],FL,FL).
falsify_vars([V|Vs],FLAcc,FL) :-
    append(FLAcc,[V#=0],FLAcc2),
    falsify_vars(Vs,FLAcc2,FL).


% has_skills(+Employee,+Skills)
%
% Fails if Employee does not possess all Skills.
has_skills(_,[]).
has_skills(Employee,[Skill|Skills]) :-
	skill(Employee,Skill),
	has_skills(Employee,Skills).

