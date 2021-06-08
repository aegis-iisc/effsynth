exception ParserError of string 
open Printf 
open SpecLang
module TypeSpec= RelSpec.TypeSpec 
module Formula = RelSpec.Formula
module TEnv = Environment.TypingEnv 
module ConsEnv = Environment.Constructors

exception LexingError of string 
let load_file f =
  let ic = open_in f in
  let n = (in_channel_length ic) in
  let s = really_input_string ic n in 
  close_in ic;
  (s)

(*Lex and Parse the specification file*)
let lexAndParseLSpec s= 
    let lexbuf = 
      try 
      Lexing.from_string s  
      with 
      | _ -> raise (ParserError "Error in Lexing ")
    in   
    let v = Lexing.lexeme lexbuf in 
    
    let ast = 
      try 
       SpecParser.start SpecLexer.token lexbuf 
      with 
      | e -> raise (e) 
    in
    ast 

(* print the ast*)
let parseLSpecFile file = 
    let s = load_file file in 
     Printf.printf "%s" s; 
    try
      let ast = lexAndParseLSpec s in            
      ast
    with 
    | e -> raise e


(*Populate the Gamma, Formulas, and Sigma*)
let elaborateEnvs ast = 
 let RelSpec.T {typespecs;preds;_} = ast in 
 let gamma = TEnv.empty in
 let sigma = ConsEnv.empty in 

 let gamma  = List.fold_left (fun tmap ts -> let TypeSpec.T{ name;refty;_} = ts in                                      
                               let stringName = Var.toString name in 
                               if stringName = "goal" then 
                                  tmap 
                              else 
                               TEnv.add tmap stringName refty) gamma typespecs in
 let goalTypespec = List.find (fun ts -> let TypeSpec.T{name;refty;_} = ts in 
                        if name = "goal" then true else false) typespecs in 
 let TypeSpec.T{name;refty;_} = goalTypespec in 
 let goal = refty in 
 (*TODO populate sigma*)
 (gamma, sigma, goal)

