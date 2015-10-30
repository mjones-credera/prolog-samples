% By Micah Jones
%
% New version to use shifts instead of hours
%
% For more real world applications of Prolog and CLP in particular, see:
% http://4c.ucc.ie/~hsimonis/ccl2.pdf

employee(micah).
employee(jonathan).
employee(blake).

max_shifts(micah,10).
max_shifts(jonathan,12).
max_shifts(blake,10).

weekend(saturday).
weekend(sunday).

max_weekend_shifts(micah,1).
max_weekend_shifts(jonathan,2).
max_weekend_shifts(blake,1).

skill(micah,programming).
skill(micah,writing).
skill(micah,speaking).
skill(jonathan,programming).
skill(jonathan,babysitting).
skill(jonathan,writing).
skill(blake,programming).
skill(blake,speaking).

task_skills(documentation,[programming,writing]).
task_skills(web_design,[programming]).
task_skills(presentation,[speaking]).

unavailable(micah,shift(friday,1)).
unavailable(micah,shift(friday,2)).
unavailable(micah,shift(saturday,1)).
unavailable(micah,shift(saturday,2)).



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

task(web_design,shift(monday,1)).
task(web_design,shift(monday,2)).
task(web_design,shift(tuesday,1)).
task(web_design,shift(tuesday,2)).
task(web_design,shift(wednesday,1)).
task(web_design,shift(wednesday,2)).
task(web_design,shift(thursday,1)).
task(web_design,shift(thursday,2)).
task(web_design,shift(friday,1)).
task(web_design,shift(friday,2)).

task(presentation,shift(friday,1)).


% schedule(-Schedule)
%
% Schedule is of the format [assignment(Employee,TaskName,Day,Shift),...]
schedule(Schedule) :-
	bagof(task(TaskName,Shift),task(TaskName,Shift),Tasks),
	bagof(Employee,employee(Employee),Employees),
	schedule(Tasks,Employees,[],Schedule).

% schedule(+TaskList,+Employees,+ScheduleAcc,-Schedule)
schedule([],_,Schedule,Schedule) :- writeln(Schedule).
schedule([Task|Tasks],Employees,ScheduleAcc,Schedule) :- 
	schedule_task(Task,Employees,ScheduleAcc,ScheduleAcc2),
	schedule(Tasks,Employees,ScheduleAcc2,Schedule).

% schedule_task(+Task,+Employees,+ScheduleAcc,-Schedule)
schedule_task(task(TaskName,shift(Day,Shift)),Employees,ScheduleAcc,Schedule) :-
	member(Employee,Employees),
	can_assign(Employee,ScheduleAcc,TaskName,Day,Shift),
	append(ScheduleAcc,[assign(Employee,TaskName,Day,Shift)],Schedule).

% can_assign(+Employee,+Schedule,+TaskName,+Day,+Shift)
%
% Fails if Employee cannot take the given TaskName at that Shift on that Day.
% Checks the following constraints:
%
% 1. They must have the necessary skills for the TaskName
% 2. They cannot be listed as unavailable for the given Shift
% 3. They cannot already be assigned elsewhere in the Schedule
% 4. They cannot exceed their max_shifts for the week
can_assign(Employee,Schedule,TaskName,Day,Shift) :-
	% 1. Check skills
	task_skills(TaskName,Skills),
	has_skills(Employee,Skills),

	% 2. Check availability
	\+(unavailable(Employee,shift(Day,Shift))),
	
	% 3. Check if the employee has already been assigned
	\+(member(assign(Employee,_,Day,Shift),Schedule)),
	
	% 4. Have we exceeded our max shifts for the week?
	check_max_shifts(Employee,Schedule),
	
	% 5. Have we exceeded our max weekend shifts for the week?
	check_max_weekend_shifts(Employee,Schedule).
	

% has_skills(+Employee,+Skills)
%
% Fails if Employee does not possess all Skills.
has_skills(_,[]).
has_skills(Employee,[Skill|Skills]) :-
	skill(Employee,Skill),
	has_skills(Employee,Skills).

% check_max_shifts(+Employee,+Schedule)
%
% Fails if the employee has matched or exceeded their max_shifts.
check_max_shifts(Employee,Schedule) :-
	findall(Employee,(member(assign(Employee,_,_,_),Schedule)),EmployeeAppearances),
	length(EmployeeAppearances,Count),
	max_shifts(Employee,MaxShifts),
	Count =< MaxShifts.
	
% check_max_weekend_shifts(+Employee,+Schedule)
%
% Fails if the employee has too many weekend shifts.
check_max_weekend_shifts(Employee,Schedule) :-
	findall(Employee,(weekend(WeekendDay),member(assign(Employee,_,WeekendDay,_),Schedule)),EmployeeAppearances),
	length(EmployeeAppearances,Count),
	max_weekend_shifts(Employee,MaxShifts),
	Count =< MaxShifts.
   