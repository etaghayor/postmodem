
type 'a laterType = Next of (unit -> 'a);;

let next x = Next (fun () -> x);;
let prev (Next f) = f ();;


type proc = { run : 'a. (unit -> 'a) -> ((unit -> proc) -> 'a) -> 'a };;

let halt : proc = (*fold*){ run = fun d _ -> d () };;

let cont f : proc = (*fold*) { run = fun _ c -> c f};;

let rec inf1 () = cont (*fold*) (fun () -> (print_string "seen "; inf1 ()));;

let rec take1 p =
  p.run (*unfold p*) (fun () -> print_string "unseen.") (fun f -> take1 (f ()));;


type procLater = { run : 'a. (unit -> 'a) -> ((unit -> procLater laterType) -> 'a) -> 'a };;
let haltLater : procLater = { run = fun d _ -> d () };;
let contLater f : procLater = { run = fun _ c -> c f };;

let rec inf2 () = contLater (fun () -> (print_string "seen "; next (inf2 ())));;
let rec take2 p =
  p.run (fun () -> print_string "unseen.") (fun f -> take2 (prev (f ())));;




type procedure = Halt | GoodInfinity of (unit -> procedure)


let rec goodInf =
  GoodInfinity
    (fun () ->
       print_string "seen ";
       goodInf)

let rec goodTake = function
  | Halt -> print_string "unseen"
  | GoodInfinity f -> goodTake (f ());;
