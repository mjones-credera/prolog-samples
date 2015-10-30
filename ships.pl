:- use_module(library(clpfd)).

ship(maria).
ship(victoria).
ship(elsa).

capacity(maria,5).
capacity(victoria,4).
capacity(elsa,3).

%container(Name,Size,AvailableTime,Destination)
container(a,2,3,boston).
container(b,4,7,baltimore).
container(c,1,10,boston).
container(d,1,16,miami).
container(e,4,17,baltimore).

travel_time(origin,miami,5).
travel_time(origin,boston,3).
travel_time(origin,baltimore,1).
travel_time(miami,boston,8).
travel_time(miami,baltimore,6).
travel_time(boston,miami,8).
travel_time(boston,baltimore,2).
travel_time(baltimore,miami,6).
travel_time(baltimore,boston,2).


% schedule_earliest_finish(-EarliestSchedule,-EndTime)
%
% Obtains all possible schedules and determines which is the one that ends the earliest
% based on dropoff times. (Note that if there are any ties, the first listed schedule wins.)
schedule_earliest_finish(EarliestSchedule,EndTime) :-
    findall(Schedule,schedule(Schedule),Schedules),
    get_max_schedule_times(Schedules,[],ScheduleTimes),
    ScheduleTimes = [CurrentEarliestScheduleTime|ScheduleTimesTail],
    get_earliest_schedule(ScheduleTimesTail,CurrentEarliestScheduleTime,EarliestScheduleTime),
    EarliestScheduleTime = schedule_max_time(EarliestSchedule,EndTime).

% get_max_schedule_times(+Schedules,+ScheduleTimesAcc,-ScheduleTimes)
%
% ScheduleTimes is a list with elements of the form schedule_max_time(Schedule,MaxTime).
get_max_schedule_times([],ScheduleTimes,ScheduleTimes).
get_max_schedule_times([Schedule|Schedules],ScheduleTimesAcc,ScheduleTimes) :-
    findall(Time,(
        member(schedule(_,Events),Schedule),
        member(dropoff(_,_,Time),Events)
        ),Times),
    max_list(Times,MaxTime),
    append(ScheduleTimesAcc,[schedule_max_time(Schedule,MaxTime)],ScheduleTimesAcc2),
    get_max_schedule_times(Schedules,ScheduleTimesAcc2,ScheduleTimes).

% get_earliest_schedule(+ScheduleTimes,+CurrentEarliestScheduleTime,-EarliestScheduleTime)
get_earliest_schedule([],EarliestScheduleTime,EarliestScheduleTime).
get_earliest_schedule([schedule_max_time(Schedule,Time)|ScheduleTimes],
        schedule_max_time(CurrentEarliestSchedule,CurrentEarliestTime),EarliestScheduleTime) :-
    ((Time #< CurrentEarliestTime) ->
        get_earliest_schedule(ScheduleTimes,schedule_max_time(Schedule,Time),EarliestScheduleTime) ;
        get_earliest_schedule(ScheduleTimes,schedule_max_time(CurrentEarliestSchedule,CurrentEarliestTime),EarliestScheduleTime)).
    

% schedule(-Schedule)
%
% Schedule is list of schedule(Ship,Events).
% Events is a list where each element is one of the following:
%     pickup(ContainerName,Location,Time)
%     travel(Location1,Location2,ArrivalTime),
%     dropoff(ContainerName,Location,Time)
schedule(Schedule) :-
	findall(Ship,ship(Ship),Ships),
    findall(container(ContainerName,Size,AvailableTime,Destination),container(ContainerName,Size,AvailableTime,Destination),Containers),
    load_ships(Containers,Ships,[],ShipCargos),
	schedule(ShipCargos,[],Schedule).

% load_ships(+Containers,+Ships,+ShipCargosAcc,-ShipCargos)
%
% Calculates ship cargo configurations based on ship capacities and container sizes.
load_ships([],[],ShipCargos,ShipCargos).
load_ships(Containers,[Ship|Ships],ShipCargosAcc,ShipCargos) :-
    Containers \= [],
    capacity(Ship,Capacity),
    subset(Containers,Cargo),
    findall(Size,member(container(_,Size,_,_),Cargo),Sizes),
    sum(Sizes,#=<,Capacity),
    append(ShipCargosAcc,[cargo(Ship,Cargo)],ShipCargosAcc2),
    subtract_once(Containers,Cargo,RemainingContainers),
    load_ships(RemainingContainers,Ships,ShipCargosAcc2,ShipCargos).

% schedule(+ShipCargos,+ScheduleAcc,-Schedule)	
schedule([],Schedule,Schedule).
schedule([cargo(_,[])|ShipCargos],ScheduleAcc,Schedule) :-
    % Skip this ship if it has an empty cargo
    schedule(ShipCargos,ScheduleAcc,Schedule).
schedule([cargo(Ship,Containers)|ShipCargos],ScheduleAcc,Schedule) :-
    Containers \= [],
    % Add pickup operations for the cargo
    schedule_pickups(Containers,[],PickupEvents),
    % Get the latest available time on the containers to know when we'll leave
    findall(AvailableTime,member(container(_,_,AvailableTime,_),Containers),AvailableTimes),
    max_list(AvailableTimes,LatestTime),
    % Figure out a route that gets everywhere we need to go and add to the schedule
    schedule_route(Containers,origin,LatestTime,[],Events),
    append(PickupEvents,Events,ShipEvents),
    append(ScheduleAcc,[schedule(Ship,ShipEvents)],ScheduleAcc2),
    schedule(ShipCargos,ScheduleAcc2,Schedule).

% schedule_pickups(+Containers,+PickupEventsAcc,-PickupEvents)
schedule_pickups([],PickupEvents,PickupEvents).
schedule_pickups([container(ContainerName,_,Time,_)|Containers],PickupEventsAcc,PickupEvents) :-
    append(PickupEventsAcc,[pickup(ContainerName,origin,Time)],PickupEventsAcc2),
    schedule_pickups(Containers,PickupEventsAcc2,PickupEvents).
    
% schedule_route(+Containers,+CurrentLocation,+CurrentTime,+EventsAcc,-Events)
schedule_route([],_,_,Events,Events).
schedule_route(Containers,Location,Time,EventsAcc,Events) :-
    Containers \= [],
    % Schedule any dropoffs that would occur at the current location
    schedule_dropoffs(Containers,Location,Time,[],DropoffEvents,[],NewCargo),
    schedule_travel(NewCargo,Location,NewLocation,Time,NewTime,[],TravelEvents),
    append(DropoffEvents,TravelEvents,NewEvents),
    append(EventsAcc,NewEvents,EventsAcc2),
    schedule_route(NewCargo,NewLocation,NewTime,EventsAcc2,Events).
    
% schedule_dropoffs(+Containers,+Location,+Time,+DropoffEventsAcc,-DropoffEvents,+NewCargoAcc,-NewCargo)
%
% For every container destined for this location, create a dropoff event.
% NewCargo contains any containers not dropped off here.
schedule_dropoffs([],_,_,DropoffEvents,DropoffEvents,NewCargo,NewCargo).
schedule_dropoffs([Container|Containers],Location,Time,
        DropoffEventsAcc,DropoffEvents,NewCargoAcc,NewCargo) :-
    Container = container(ContainerName,_,_,Location),
    % This container is destined for this location; drop it off
    append(DropoffEventsAcc,[dropoff(ContainerName,Location,Time)],DropoffEventsAcc2),
    schedule_dropoffs(Containers,Location,Time,DropoffEventsAcc2,DropoffEvents,NewCargoAcc,NewCargo).
schedule_dropoffs([Container|Containers],Location,Time,
        DropoffEventsAcc,DropoffEvents,NewCargoAcc,NewCargo) :-
    Container = container(_,_,_,Destination),
    Destination \= Location,
    % This container goes elsewhere, add it to the NewCargoAcc
    append(NewCargoAcc,[Container],NewCargoAcc2),
    schedule_dropoffs(Containers,Location,Time,DropoffEventsAcc,DropoffEvents,NewCargoAcc2,NewCargo).

% schedule_travel(+Containers,+CurrentLocation,-NewLocation,+CurrentTime,-NewTime,+TravelEventsAcc,-TravelEvents)
schedule_travel([],Location,Location,Time,Time,TravelEvents,TravelEvents).
schedule_travel(Containers,CurrentLocation,NewLocation,CurrentTime,NewTime,TravelEventsAcc,TravelEvents) :-
    Containers \= [],
    member(container(_,_,_,NewLocation),Containers),
    travel_time(CurrentLocation,NewLocation,TravelTime),
    NewTime is CurrentTime+TravelTime,
    append(TravelEventsAcc,[travel(CurrentLocation,NewLocation,NewTime)],TravelEvents).
    
    
%get_subset(List,Subset) :-
%    length(List,L),
%    length(Indices,SubsetSize),
%    SubsetSize#>=0,SubsetSize#=<L,
%    Indices ins 1..L,all_different(Indices),label(Indices),
%    get_indices(List,Indices,SubList).
    
%get_indices(List,Indices,Sublist) :-
    

% subset(+List,-Subset)
%
% Returns all ordered subsets of the given list.
subset([], []).
subset([E|Tail], [E|NTail]):-
  subset(Tail, NTail).
subset([_|Tail], NTail):-
  subset(Tail, NTail).

% subtract_once(+List,+DeleteList,-NewList)
%
% Removes each element from DeleteList from List. Unlike the predicate from the lists
% library, this only removes the first instance of each element in DeleteList from List.  
subtract_once(List, [], List).
subtract_once(List, [Item|Delete], Result):-
  (select(Item, List, NList)->
    subtract_once(NList, Delete, Result);
    (List\=[],subtract_once(List, Delete, Result))).
  
