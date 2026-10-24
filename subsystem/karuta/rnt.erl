%% Tuples of an RNT relation, as Translator.ml writes and reads them:
%% a tuple is {Type, #{Name => Value}}, its type, names, bitstrings
%% and its integers no wider than an OCaml int.
-module(rnt).
-export([recv/1, send/1]).

-define(MIN_INT, -(1 bsl 62)).
-define(MAX_INT, (1 bsl 62) - 1).

%% A tuple from the bytes RNT sent
recv(Bytes) -> holdable(binary_to_term(Bytes, [safe])).

%% The bytes RNT reads a tuple from
send(Tuple) -> term_to_binary(holdable(Tuple)).

%% The tuple, if RNT can hold it
holdable({Type, Attributes} = Tuple) when is_binary(Type), is_map(Attributes) ->
    case lists:all(fun attribute/1, maps:to_list(Attributes)) of
        true -> Tuple;
        false -> error(badarg, [Tuple])
    end;
holdable(Tuple) -> error(badarg, [Tuple]).

attribute({Name, Value}) when is_binary(Name), is_binary(Value) -> true;
attribute({Name, Value}) when is_binary(Name), is_integer(Value) ->
    Value >= ?MIN_INT andalso Value =< ?MAX_INT;
attribute(_) -> false.
