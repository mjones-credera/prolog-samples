person(micah).
person(jonathan).

likes(micah,hamburgers).
likes(micah,smashbros).
likes(jonathan,dolphins).

person_likes(Name,Thing) :- person(Name),likes(Name,Thing).

% which_people_like(+Things,+PeopleLikeAcc,-PeopleLike)
which_people_like([],PersonLike,PersonLike).
which_people_like([Thing|Things],PeopleLikeAcc,PeopleLike) :-
    findall(Person,likes(Person,Thing),People),
    append(PeopleLikeAcc,[people_like(People,Thing)],PeopleLikeAcc2),
    which_people_like(Things,PeopleLikeAcc2,PeopleLike).
