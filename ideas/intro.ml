

(* Normal Halt case *)
type proc1 = { unfold : 'a.  'a -> ((unit -> proc1) -> 'a) -> 'a };;

let halt1 : proc1 = (*fold*){ unfold = fun d _ -> d };;

let cont1 f : proc1 = (*fold*) { unfold = fun _ c -> c f};;

let rec inf1 ():proc1 = cont1 (*fold*) (fun () -> (print_string "seen "; inf1 ()));;

let rec take1 p =
  p.unfold (*unfold p*) (print_string "unseen.") (fun f -> take1 (f ()));;

(* 
let rec take2 p =
   p.unfold (*unfold p*) (fun () -> print_string "unseen.") (fun f -> take2 (f ()));;
 *)




(* Later *)
type 'a laterType = Next of (unit -> 'a);;

let next x = Next (fun () -> x);;
let prev (Next f) = f ();;


type procLater = { run : 'a. (unit -> 'a) -> ((unit -> procLater laterType) -> 'a) -> 'a };;

let haltLater : procLater = { run = fun d _ -> d () };;
let contLater f : procLater = { run = fun _ c -> c f };;

let rec infLater () = contLater (fun () -> (print_string "seen "; next (infLater ())));;
let rec takeLater p =
  p.run (fun () -> print_string "unseen.") (fun f -> takeLater (prev (f ())));;


(* Reference *)

type procedure = Halt | GoodInfinity of (unit -> procedure)

let rec goodInf =
  GoodInfinity
    (fun () ->
       print_string "seen ";
       goodInf)

let rec goodTake = function
  | Halt -> print_string "unseen"
  | GoodInfinity f -> goodTake (f ());;

let rec lazyTake = function
  | Halt -> fun () -> print_string "unseen"
  | GoodInfinity f -> lazyTake (f ());;



(* Delay Halt case *)
type proc3 = { run : 'a. (unit -> 'a) -> ((unit -> proc3) -> 'a) -> 'a };;

let halt3 : proc3 = (*fold*){ run = fun d _ -> d () };;

let cont3 f : proc3 = (*fold*) { run = fun _ c -> c f};;

let rec inf3 () = cont3 (*fold*) (fun () -> (print_string "seen "; inf3 ()));;

let rec take3 p =
  p.run (*unfold p*) (fun () -> print_string "unseen.") (fun f -> take3 (f ()));;



(* --------------------------- *)
(* Game Example *)

type game = Start | Play of (int -> game)

let rec playGame n = function
  | Start -> (Printf.sprintf "Finish! %d" n) |> print_string
  | Play f ->
    playGame (n-1) (f (n-1));;

type 'a gameC = { unfold : 'a -> ((int -> 'a gameC) -> 'a) -> 'a };;

let start : 'a gameC = 
  { unfold = fun s_fun _ -> s_fun };;
let play f: 'a gameC = 
  { unfold = fun _ p_fun -> p_fun f};;

let rec playGameC n g =
  g.unfold
    (Printf.sprintf "Finish! %d\n" n |> print_string)
    (fun d -> playGameC (n-1) (d (n-1)));;
