(*
This is the notes from lab 10.

In lab10 went over a "clever" solution to part 2 that very few people attempted, where Begin ... End regions are stored in a single Block constructor.
The primary trade off we make with this aproach is, runing is easier, and parsing is harder.
I chose this solution to present becuase I suspect it will be helpful for part 3.

There is a complete solution to part 2 availible in the resources section under piazza: https://piazza.com/bu/fall2019/cs320/resources
That solution gives an implementation more in line with the lecture slides, and the recomendations we made on piazza.
*)

(* 
recall how Begin..End is specified

for environments


	a = 1
	Begin
				a =? 1
	a = 2
				a =? 2
	End
				a = ?1


where a=1 is a shorthand for 
PushI (I 1)
PushN (N "a")
Bind

begin end blocks can see prevous assignments but those assignments are "forgotten" when outside of the block


for Stacks

	PushI (I 1)
	PushI (I 1)
	Begin
	Add			will push an error onto the stack
	PushI (I 2)
	End			return to the old stack with the final value of PushI (I 2) at the top 
	Add         add 2 and 1
	
begin and end blocks operate in an empty stack
*)


(* things that goes on a stack *)
type   stackVal = 
   I of int 
  | S of string 
  | N of string
  | B of bool 
  | U
  | E
  | Func of (string *  func ) 
  | FuncInOut of (string * func)
  | Return of stackVal
(* But we will also use this for binding variables, 
   as long as we remember variables cannot be bound to errors, or directly to names *)
  

(* well formed instructions *)
and command = PushI of   stackVal 
             | PushS of   stackVal 
             | PushN of   stackVal 
             | PushB of   stackVal
             | Push of    stackVal
             | Add | Sub | Mul | Div | Rem | Neg
             | Concat
             | And | Or | Not
             | Equal | LessThan
             | If
             | Pop
             | Swap
             | Block of  command list (* handle blocks together *)
             | Bind
             | Return
             | FunEnd
             | Call
             | Fun of ( stackVal *stackVal)
             | InOutFun of  (stackVal * stackVal)
             | Quit


(* If we limit our interactions with the environment to these helper functions, we can safely change how we encode the environment without changing much other code *)
and   env = (string *  stackVal) list
and  func = ( stackVal *  stackVal *  command list * env )
type ful = func list
let insert (s:string)  (sv : stackVal) (env: env) : env = (s,sv)::env

let rec fetch (name :string)  (env: (string * stackVal) list) : stackVal option = 
    match env with
      | (name' , v) :: rest -> if name = name' then Some v else fetch name rest
      | []                  -> None
      
let empEnv = []

let rec funhelper (rest:command list) (n:string) (name:stackVal)   counter  (env:env): (command list * func) = 
  match rest with
  | [] -> ([],(N n,name,[],env))
  | FunEnd::restl-> if (counter == 0) then (restl,(N n,name,[],env)) else let (l,(b,c,e,f))=(funhelper restl n name   (counter -1) env) in
               (l,(b,c,FunEnd::e,f))  
  | Fun (z,y)::restl->  let (l,(b,c,d,f))=(funhelper restl n name  (counter + 1) env) in
               (l,(b,c,Fun (z,y)::d,f))  
  | InOutFun (z,y)::restl->  let (l,(b,c,d,f))=(funhelper restl n name  (counter + 1) env) in
               (l,(b,c,InOutFun (z,y)::d,f))  
  | a::restl-> let (l,(b,c,d,f))=(funhelper restl n name  counter env) in
               (l,(b,c,a::d,f))  


       

let rec run (commands : command list) (stack: stackVal list) (env: env) (ful : ful): (stackVal list* (string * stackVal) list * ful)= 
  (* if stackVal is a variable what  does it resolve to in the current environment *)
  let res (sv : stackVal) : stackVal = 
    match sv with 
      | N n -> (match fetch n env with  
                  | Some n' -> n' 
                  | None    -> N n)
      | sv -> sv
  in let bad rest :  (stackVal list* (string * stackVal) list * ful)  = run rest (E :: stack) env ful(* everything fails in the same way*)
  in match (commands , stack)  with
  | (Quit        :: _   , _         ) -> (stack,env,ful)
  | ([]                 , _         ) ->  (stack,env,ful)
  
  | (PushI (I i) :: rest, _         ) -> run rest (I i :: stack) env ful
  
  | (PushS (S s) :: rest, _         ) -> run rest (S s :: stack) env ful
  
  | (PushN (N n) :: rest, _         ) -> run rest (N n :: stack) env ful
  
  | (PushB (B b) :: rest, _         ) -> run rest (B b :: stack) env ful
  
  | (Push U      :: rest, _         ) -> run rest (U :: stack) env ful
  | (Push E      :: rest, _         ) -> run rest (E :: stack) env ful
  
  | (Add         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I j) -> run rest (I (i+j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Sub         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I j) -> run rest (I (i-j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Mul         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I j) -> run rest (I (i*j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Div         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I 0) -> bad rest
                                          | (I i, I j) -> run rest (I (i/j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Rem         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I 0) -> bad rest
                                          | (I i, I j) -> run rest (I (i mod j) :: s') env ful 
                                          | _ -> bad rest)
  
  | (Neg         :: rest, x :: s'   ) -> (match (res x) with 
                                          | (I i) -> run rest (I (-i) :: s') env ful
                                          | _ -> bad rest)

  | (Concat      :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (S i, S j) -> run rest (S (i ^ j) :: s') env ful
                                          | _ -> bad rest)
  
  | (And         :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (B i, B j) -> run rest (B (i && j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Or          :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (B i, B j) -> run rest (B (i || j) :: s') env ful
                                          | _ -> bad rest)
  
  | (Not         :: rest, x :: s'   ) -> (match (res x) with 
                                          | (B i) -> run rest (B (not i) :: s') env ful
                                          | _ -> bad rest)
  
  | (Equal       :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I j) -> run rest (B (i = j) :: s') env ful
                                          | _ -> bad rest)
  | (LessThan    :: rest, x ::y ::s') -> (match (res x, res y) with 
                                          | (I i, I j) -> run rest (B (i < j) :: s') env ful
                                          | _ -> bad rest)
                                             
  | (If          :: rest,x::y::z::s') -> (match res z with 
                                          | B true  -> run rest (y :: s') env ful
                                          | B false -> run rest (x :: s') env ful
                                          | _ -> bad rest)
  
  | (Pop         :: rest, _ :: s'   ) -> run rest s' env ful
  
  | (Swap        :: rest, x ::y ::s') -> run rest (y::x::s') env ful
  
  
  | (Bind        :: rest, N n::x::s') -> (match res x with
                                          | E   -> bad rest
                                          | N _ -> bad rest
                                          | sv  -> run rest (U::s') (insert n sv env) ful) 
  
  | (Block ls    :: rest, s'        ) -> let (top :: _,_,_) = run ls [] env ful(* an exception will be thown if the resulting stack is empty *)
                                         in  run rest (top :: s') env ful

  | (Fun (N n, name)::rest, _) -> let (comm  ,afun) = funhelper rest n name  0 env in 
                                    run comm (U::stack) ((n, Func (n, afun))::env) ful
  | (InOutFun (N n, name)::rest, _) -> let (comm  ,afun) = funhelper rest n name  0 env in 
                                    run comm (U::stack) ((n, FuncInOut (n, afun))::env) ful
  | (Call        :: rest, x::y:: s') -> (match (res x , res y) with
                                        | (E,_) -> bad rest
                                        | (N _,_) -> bad rest
                                        | (sv, Func (funname, (N a1, N a2, a3 ,a4))) -> let (return :: _,env',_) = run a3 s' ((a2,sv)::(a4 @ env)) ful in 
                                                                                        (match return with 
                                                                                         | Return top ->(match top with
                                                                                             | N n-> (match fetch n env' with
                                                                                                   
                                                                                                    | None  -> bad rest
                                                                                                   | Some Func (a,b) -> run rest ( N n::s')  ((n,Func(a,b))::env) ful
                                                                                                    | Some FuncInOut (a,b) -> run rest ( N n::s')  ((n,FuncInOut(a,b))::env) ful
                                                                                                   | Some some -> run rest (some::s') env ful )
                                                                                              | E -> run rest (E::s') env ful
                                                                                              | some -> run rest (some::s') env ful )
                                                                                          | _ -> run rest s' env ful )
                                        | (sv, FuncInOut (funname, (N a1, N a2, a3 ,a4))) -> let (return :: _,env',_) = run a3 s' ((a2,sv)::(a4@env)) ful in 
                                                                                        (match return with 
                                                                                         | Return top -> ( match (top , fetch a2 env',x) with
                                                                                              | (N n, Some somefec, N somename )-> (match fetch n env' with
                                                                                               
                                                                                                | None  -> run rest s' ((somename,somefec)::env) ful
                                                                                                | Some Func (a,b) -> run rest ( N n::s')  ((somename,somefec)::(n,Func(a,b))::env) ful
                                                                                                | Some FuncInOut (a,b) -> run rest ( N n::s')  ((somename,somefec)::(n,FuncInOut(a,b))::env) ful
                                                                                                | Some some -> run rest (some::s') ((somename,somefec)::env) ful )
                                                                                              | (some,Some somefec, N somename ) -> run rest (some::s') ((somename,somefec)::env) ful )
                                                                                        | _ -> (match (fetch a2 env',x) with
                                                                                                | (Some somefec, N somename )->  run rest s' ((somename,somefec)::env) ful)
                                                                                                | _ -> bad rest)
                                                                                                 


                                        | _-> bad rest ) 
  | (Return      :: rest, x::s) -> ((Return x ::stack),env, ful)
  | (_           :: rest, _         ) -> bad rest



  
  
(* remember to test! *)

(* ... *)


(* writing *)
let to_string (s : stackVal) : string = 
  match s with
  | I i -> string_of_int i 
  | S s  -> s
  | N n -> n
  | B b -> "<" ^ string_of_bool b ^ ">"
  | U   -> "<unit>"
  | E   -> "<error>"
  


(* parser combinators over exploded strings *)
let explode (s:string) : char list =
  let rec expl i l =
    if i < 0 
    then l 
    else expl (i - 1) (String.get s i :: l)
  in expl (String.length s - 1) []

let implode (cl:char list) : string = 
  String.concat "" (List.map (String.make 1) cl)

 
let is_alpha (c:char): bool = 
  (Char.code 'a' <= Char.code c && Char.code c <= Char.code 'z')
  || (Char.code 'A' <= Char.code c && Char.code c <= Char.code 'Z')

let is_digit (c:char): bool = 
 Char.code '0' <= Char.code c && Char.code c <= Char.code '9'

let rec take_while' (p: 'a -> bool) (es : 'a list) : ('a list) * ('a list) = 
  match es with
  | []      -> ([],[])
  | x :: xs -> if p x then let (chars, rest) = take_while' p xs in  (x :: chars, rest) else ([], x :: xs)

let take_while (p:char -> bool) (s:string) : string * string = 
  let (echars, erest) = take_while' p (explode s) 
  in (implode echars, implode erest)


let parse_int (s : string) : int option = 
    match int_of_string s with    
    | n -> Some n
    | exception _ -> None

let parse_string (s : string) : string option = 
    if String.length s > 1 && String.get s 0 = '"' && String.get s (String.length s - 1) = '"'
    then  Some (String.sub s 1 (String.length s - 2)) (* this is less restrictive then the spec *)
    else None


let parse_name (s : string) : string option = 
    if String.length s > 0 && ( let c = (String.get s 0) in is_alpha c ||  c = '_')
    then  Some s (* this is less restrictive then the spec *)
    else None
    
    
    
let parse_constant (s:string) : stackVal = 
    let s' = String.trim s in
    match s' with
    | "<true>"  -> B true
    | "<false>" -> B false
    | "<unit>"  -> U
    | _ -> match parse_int s' with
           | Some i -> I i
           | None -> match parse_string s' with
                     | Some s -> S s
                     | None -> match parse_name s' with
                               | Some s -> N s
                               | None -> E

let split_on_char (sep:char) (s: string) : string list = 
  let rec loop sep1 i part = 
    if  i < (String.length s) 
	then let c = String.get s i 
	     in if  c == sep1
	        then part :: (loop '' (i+1) "")
		    else (loop sep1 (i+1) (part ^ String.make 1 c ))
	else  [part]
  in loop sep 0 "";;


let checkfun (m:string) : (stackVal * stackVal) = 
  match split_on_char ' ' m with
  | x::y::rl -> (match split_on_char ' ' y with
                 | name::n::r-> (N name ,N n ))



let parse_single_command (s:string) : command = 
    match take_while is_alpha (String.trim s) with
    | ("PushI"   , p) -> PushI (parse_constant p)
    | ("PushS"   , p) -> PushS (parse_constant p)
    | ("PushN"   , p) -> PushN (parse_constant p)
    | ("PushB"   , p) -> PushB (parse_constant p)
    | ("Push"    , p) -> Push (parse_constant p)
    | ("Add"     , _) -> Add
    | ("Sub"     , _) -> Sub
    | ("Mul"     , _) -> Mul
    | ("Div"     , _) -> Div
    | ("Rem"     , _) -> Rem
    | ("Neg"     , _) -> Neg
    | ("Pop"     , _) -> Pop
    | ("Swap"    , _) -> Swap
    | ("Concat"  , _) -> Concat
    | ("And"     , _) -> And
    | ("Or"      , _) -> Or
    | ("Not"     , _) -> Not
    | ("LessThan", _) -> LessThan
    | ("Equal"   , _) -> Equal
    | ("If"      , _) -> If
    | ("Bind"    , _) -> Bind
    | ("Fun"     , m) -> Fun (checkfun m)
    | ("InOutFun", m) -> InOutFun (checkfun m)
    | ("Return"  , _) -> Return
    | ("FunEnd"  , _) -> FunEnd
    | ("Call"    , _) -> Call
    | ("Quit"    , _) -> Quit
    (* any unknown commands will result in an exception *)

 
(* parsing becomes harder, though it is doable with a "claver" helper function 
this function had the name parse_block in lab 1 and 2.
*)
 
(* group together everything till you see an "End" return the rest for future work *)
let rec parse_until_end (ls :string list) :  (command list) * (string list)  =  
    match ls with 
    | []              -> ([], [])
    
    | "End" ::     tl ->  ([], tl)
    | "Begin" ::     tl ->  let (cls, rest) = parse_until_end tl
                            in let block = Block cls
                            in let (cls', rest') = parse_until_end rest
                            in (block :: cls', rest')
    
    | h ::     tl         -> let com = parse_single_command h
                             in let (cls, rest) = parse_until_end tl
                             in (com :: cls, rest)
  
let parse_commands (ls :string list) : command list =
  let (coms, _) = parse_until_end ls 
  in coms


let rec read_lines (ch : in_channel) : string list =
  match input_line ch with 
    | str                    -> str :: read_lines ch
    | exception  End_of_file -> [] (* input_line throws an exception at the end of the file *)
    
    
(* from lab 3 *)
let rec write_lines (ch) (ls : string list ) : unit =
  match ls with
    | []      -> ()
    | x :: xs -> let _ = Printf.fprintf ch "%s\n" x in write_lines ch xs
    


(* run the interperter on the commands in inputFile and write the resulting stack in outputFile *)
let interpreter (inputFile : string) (outputFile : string) : unit =
  let ic = open_in inputFile in
  let lines_in = List.map String.trim (read_lines ic) in
  let _ = close_in ic in
  
  let commands = parse_commands lines_in in
  let (stack,evn,_) = run commands [] [] [] in
  let lines_out = List.map to_string stack in
  
  let oc = open_out outputFile in
  let _ = write_lines oc lines_out in
  let _ = close_out oc in ()

let interpreter' (inputFile : string) (outputFile : string)  =
  let ic = open_in inputFile in
  let lines_in = List.map String.trim (read_lines ic) in
  let _ = close_in ic in
  
  let commands = parse_commands   lines_in in
  commands

(* TODO file IO stuff *)