

(* Sum Type with one variant *)
type nat = Infinity of (unit -> nat);;
let rec myInf = Infinity ( fun () -> print_string "seen. "; myInf);;
let rec take = function
	| Infinity f -> take (f ()) ;;
    
print_string "unseen";;

(* Sum Type with two variants *)

type goodNat = Halt | GoodInfinity of (unit -> goodNat);;
let rec goodInf = GoodInfinity ( fun () -> print_string "seen. "; goodInf);;
let rec goodTake = function
    | Halt -> print_string "unseen"
	| GoodInfinity f -> goodTake (f ());;

(* external recursion *)
let rec iter f = 
    f(); iter f;;
let outsideIter = function
    | Halt -> print_string "unseen"
	| GoodInfinity f -> iter f;;


type goodNat = Zero | Succ of (int -> goodNat)

let rec natInf = Succ (fun n -> print_string "here. "; natInf);;
let rec iterNat f n = 
    let _ = f n in iterNat f 1;;

let unfoldNat = function
    | Zero -> 0
    | Succ f -> iterNat f 1;;

(* nested Infinity *)

type game = End | Turn of (unit -> game);;
let rec infGame = Turn ( fun () -> print_string "ping, "; Turn (fun () -> print_string "pong! "; infGame ));;
let rec play = function
    | End -> print_string "game over!"
	| Turn f -> play (f ());;


(* Sum Type with two variants of the same shape *)

type stream =
  | Left  of (unit -> stream)
  | Right of (unit -> stream)

let rec always_left =
  Left (fun () ->
    print_string "went_left";
    always_left)

let rec traverse = function
  | Left  f -> print_string "enter_left";  traverse (f ())
  | Right f -> print_string "enter_right"; traverse (f ());


type tuple = 
    | Double of (int * tuple)
    | Triple of (int * int * tuple)

let rec double = Double (1, (print_string "always 42. " ; double));;

let rec iterTuple = function
    | Double (x,y) ->  iterTuple (Double (x+1, y))
    (* | Double (x,y) ->  (Double (x+1, y+1)) *)
    | t -> t

let matchTuple = function
    | Triple (x,y,z) as t -> t
    | Double (x, y)-> iterTuple y;;

(* matchTuple double;; *)