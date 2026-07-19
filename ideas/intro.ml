
(* examples *)


type mainrec = M1 | M2 of (unit -> mainrec)
(* mainrec ≜ ∀T. (unit -> T (-)) -> ((unit -> T (+)) -> T (-)) -> T (+) *)

let rec minf = M2 (fun () -> print_string "seen "; minf);;

let rec mtake x = match x with
  | M1 -> (*x/M1 is a later => call prev *) print_string "unseen"
  | M2 f -> mtake ((*next*)f ());;

type arec = A1 of int | A2 of (arec -> unit)
(* arec ≜ ∀T. (int -> T (-))  -> ((T (-) -> unit) -> T (-)) -> T (+)*)

let rec ainf = A2 (fun x -> print_string "Aseen ");;

let rec atake x = match x with
  | A1 n ->(*x/A1 n is a later => call prev *) print_string "Aunseen"
  | A2 f  -> f (*next*)x; atake (*next*)x;;

type brec = B1 of (int -> brec -> int) | B2 of brec
(* brec ≜ ∀T. (int -> T (+) -> int)  -> (T (+) -> T (-)) -> T (+)*)
let rec binf = B1 (fun n b -> print_string "Bseen "; n);;
let rec btake x = match x with
  | B1 f -> let _ = (f 0 (*next*)x) in btake (*next*)x
  | B2 b -> (*b is a later and B2 b is negative => call prev*)print_string "Bunseen"

(* Reference *)

type procedure = Halt | GoodInfinity of (unit -> procedure)

let rec goodInf =
  GoodInfinity
    (fun () ->
       print_string "seen ";
       goodInf)

let rec goodTake x = match x with
  | Halt -> print_string "unseen"
  | GoodInfinity f -> goodTake (f ());;

let rec lazyTake = function
  | Halt -> fun () -> print_string "unseen"
  | GoodInfinity f -> lazyTake (f ());;
(* Normal Halt case *)

(* P ≜ rec α. ∀T. T -> ((unit -> ▶α) -> T) -> T*)
type proc1 = { unfold : 'a.  'a -> ((unit -> proc1) -> 'a) -> 'a };;

(* halt1 = fold (ΛT.λd.λ_.d) 
   halt1: P *)
let halt1 : proc1 = (*fold*){ unfold = fun d _ -> d };;


(* cont1 = λf. fold (ΛT.λ_.λc.c)
   cont1 : (unit -> ▶P) -> P*)
let cont1 f : proc1 = (*fold*) { unfold = fun _ c -> c f};;

(* inf1 = 
   fix (λf.λ().
        cont1 (next λ().
          let _ = ev["seen"] in
          next (f ())
          )
        ) 
   inf1 (): P & seen^ω 
*)
let rec inf1 ():proc1 = cont1 (*fold*) (fun () -> (print_string "seen "; inf1 ()));;

(* 
  take1 = 
    fix (λg.λp.
      let x1 = unfold p in
      let x2 = x1[unit] in
      let x3 = x' (ev["unseen"]) in
      let z = next ( λf.
                  let y = next () in
                  let z = g ⊛ y in
                  prev z) in
      x3 z
      ) 
  take1: ▶(P → unit & "seen"^ω) → P → unit & "unseen" 
*)
let rec take1 p =
  p.unfold (*unfold p*) (print_string "unseen.") (fun f -> take1 (f ()));;


let rec take2 p =
  p.unfold (*unfold p*) (fun () -> print_string "unseen.") (fun f -> take2 (f ()));;






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
