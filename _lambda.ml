module L = List
open Printf

(* Underlined Lambda Terms *)
type term =
    Var of string
  | Abs of string * term
  | App of term * term
  | UApp of term * term
  | LApp of term * term

(* Symbols as used in the tree representation *)
type symbol =
    V of string
  | L of string
  | A of string
  | UA of string
  (* for lifted terms only *)
  | LA of string

(* abbreviations *)
let var s = Var(s)
let abs s t = Abs(s, t)
let app t u = App(t, u)
let uapp t u = UApp(t, u)

(* term to string *)
let rec term_to_string = function
    Var(s)    -> s
  | Abs(s, t) -> "\\" ^ s ^ "." ^ (term_to_string t)
  | App(t, u) -> "(" ^ (term_to_string t) ^ ") (" ^ (term_to_string u) ^ ")"
  | UApp(t, u) -> "(" ^ (term_to_string t) ^ ")_(" ^ (term_to_string u) ^ ")"
  | LApp(t, u) -> "(" ^ (term_to_string t) ^ ")' (" ^ (term_to_string u) ^ ")"

let rec symbol_to_string = function
    | V(s) -> s
    | L(s) -> "λ" ^ s
    | A(s) -> "@"
    | UA(s) ->"_@"
    | LA(s) -> "@'"

(*
  get last element in a list
  this is relevant for the paths construction (beta case)
 *)
let rec last_element l =
  match l with
  | [] -> failwith ("error: empty list")
  | [x] -> x
  | x :: xs -> last_element xs

let rec prepend_to_lists ll l =
  match ll with
  | [] -> []
  | x :: xs -> [l @ x] @ prepend_to_lists xs l

let rec combine_lists_condition ll1 ll2 s =
  match ll1, ll2 with
  | xs, [] -> xs
  | [], _ -> []
  | x :: xs, ys -> if fst (last_element x) = fst s
                   then prepend_to_lists ys x @ combine_lists_condition xs ys s
                   else [x] @ combine_lists_condition xs ys s

(* uniq makes a list uniq. *)
let uniq = L.fold_left (fun acc hd -> if (not (L.mem hd acc)) then hd::acc else acc) []

(* Takes the union of two lists. *)
let union l1 l2 = uniq (l1@l2)

(* l1 \ l2 ... [1;2;3] \ [2;3] = [1] *)
let difference l1 l2 = L.fold_left
   (fun acc hd -> if (L.mem hd l2) then acc else hd::acc) [] l1

(* completely Removes an element from a list. *)
let remove l1 x = L.fold_left (fun acc hd -> if (hd = x) then acc else hd::acc) [] l1

(*  *)
let rec free_variables t = match t with
 | Var x -> [x]
 | Abs (x,t) -> remove (free_variables t) x
 | App (t1,t2) -> union (free_variables t1) (free_variables t2)
 | UApp (t1,t2) -> union (free_variables t1) (free_variables t2)
 | LApp (t1,t2) -> union (free_variables t1) (free_variables t2)

let bound_variables t =
 let rec variables = function
   | Var x -> [x]
   | Abs (x,y) -> x :: (variables y)
   | App (t1,t2) -> uniq ((variables t1)@(variables t2))
   | UApp (t1,t2) -> uniq ((variables t1)@(variables t2))
   | LApp (t1,t2) -> uniq ((variables t1)@(variables t2))
 in uniq (difference (variables t) (free_variables t))

let rec contains l s =
 match l with
 | [] -> false
 | x::xs -> if x = s then true
            else contains xs s

let rec term_paths_r term pos =
  match term with
    | Var(s) -> [[(V(s), pos)]]
    | Abs(s, t) -> prepend_to_lists (term_paths_r t (pos ^ "1")) [(L(s), pos)]
    | App(t, u) -> prepend_to_lists (term_paths_r t (pos ^ "1")) [(A("@"), pos)] @
                   prepend_to_lists (term_paths_r u (pos ^ "2")) [(A("@"), pos)]
    | LApp(t, u) -> prepend_to_lists (term_paths_r t (pos ^ "1")) [(LA("@"), pos)] @
                    prepend_to_lists (term_paths_r u (pos ^ "2")) [(LA("@"), pos)]
    | UApp(Abs(s, t), u) ->
                   if contains (free_variables t) s
                   then combine_lists_condition
                         (prepend_to_lists (term_paths_r t (pos ^ "11")) [(UA("_@"), pos); (L(s), (pos ^ "1"))])
                         (term_paths_r u (pos ^ "2")) (V(s), "")
                   else prepend_to_lists (term_paths_r t (pos ^ "1")) [(UA("_@"), pos); (L(s), pos)]
    | UApp(_, _) -> failwith ("error: wrong term syntax")


let term_paths term =
  term_paths_r term "e"

let rec flatten_tuple_list l f =
  match l with
  | [] -> []
  | x :: xs -> f x :: (flatten_tuple_list xs f)

let rec flatten_ll_tuples l f =
  match l with
  | [] -> []
  | x :: xs -> flatten_tuple_list x f :: (flatten_ll_tuples xs f)

let symbol_path path =
  flatten_tuple_list path fst

let position_path path =
  flatten_tuple_list path snd

let symbol_paths term =
  List.map symbol_path (term_paths term)

let pos_paths term =
  List.map position_path (term_paths term)

let is_prefix s1 s2 =
 let len1 = String.length s1
 and len2 = String.length s2 in
 if len1 < len2 then false else
   let sub = String.sub s1 0 len2 in
   (sub = s2)

let rec is_captured var l =
  match l with
  | [] -> false
  | (x, p) :: xs -> if x = fst var
                    then not (is_prefix (snd var) p)
                    else is_captured var xs

let rec is_bounded var l =
  match l with
  | [] -> false
  | (x, p) :: xs -> if x = fst var
                    then (is_prefix (snd var) p)
                    else is_captured var xs

let rec t_contains l s f =
 match l with
 | [] -> false
 | (x, _)::xs -> if x = f s then true
                 else t_contains xs s f

let rec t_element l s f g =
  match l with
  | [] -> failwith ("error: element not found")
  | (x, p)::xs -> if x = f s then g (x,p)
                  else t_element xs s f g

let t_uniq = L.fold_left (fun acc hd -> if (not (t_contains acc hd fst)) then hd::acc else acc) []


let rec remove_first_occurence l s f =
  match l with
  | [] -> []
  | x::xs -> if f x = s then xs
             else x :: (remove_first_occurence xs s f)

let rec capturing_edge_r path acc =
  match path with
  | [] -> []
  | (A(x), _) :: xs -> capturing_edge_r xs acc
  | (LA(x), _) :: xs -> capturing_edge_r xs acc
  | (UA(x), _) :: ((L(y), p) :: xs) ->
            if (t_contains xs (V(y), p) fst) then
              if is_prefix p (t_element xs (V(y), p) fst snd) then
                capturing_edge_r xs acc
              else
                capturing_edge_r xs ((y, p) :: acc)
            else
              capturing_edge_r xs acc
  | (UA(x), _) :: xs -> failwith ("error: inconsistent paths")
  | (L(x), p) :: xs -> capturing_edge_r xs ((x, p) :: acc)
  | (V(x), p) :: xs -> if (t_contains acc (x, p) fst) then
                          if is_captured (x,p) acc
                          then [(t_element acc (x, p) fst snd, p)]
                          else capturing_edge_r xs (remove_first_occurence acc x fst)
                       else capturing_edge_r xs acc

let capturing_edge path =
  capturing_edge_r path []

let rec check_paths paths =
  match paths with
    | [] -> [[]]
    | x :: xs -> [capturing_edge x] @ check_paths xs

let rec binding_edges_r term pos acc =
  match term with
    | Var(s) -> if (t_contains acc (L(s), pos) fst) then
                  [(t_element acc (L(s), pos) fst snd, pos)]
                else []
    | Abs(s, t) -> (binding_edges_r t (pos ^ "1") ((L(s), pos) :: acc))
    | App(t, u) -> (binding_edges_r t (pos ^ "1") acc) @
                    (binding_edges_r u (pos ^ "2") acc)
    | LApp(t, u) -> (binding_edges_r t (pos ^ "1") acc) @
                    (binding_edges_r u (pos ^ "2") acc)
    | UApp(t, u) -> (binding_edges_r t (pos ^ "1") acc) @
                    (binding_edges_r u (pos ^ "2") [])

let binding_edges term =
 binding_edges_r term "e" []

let rec all_empty l =
 match l with
 | [] -> true
 | [] :: xs -> all_empty xs
 | x :: _ -> false

let alpha_free term =
 all_empty (check_paths (term_paths term))

let rec rename_free_var term x new_name =
  match term with
  | Var(s) -> if s = x then Var(new_name) else Var(s)
  | Abs(s, t) -> if s = x then Abs(s, t)
                 else Abs(s, rename_free_var t x new_name)
  | App(t, u) -> App(rename_free_var t x new_name, rename_free_var u x new_name)
  | LApp(t, u) -> LApp(rename_free_var t x new_name, rename_free_var u x new_name)
  | UApp(t, u) -> UApp(rename_free_var t x new_name, rename_free_var u x new_name)


let rec rename_position_r term x pos =
 match term with
   | Var(s) -> if x = pos then Var("x_" ^ pos)
               else Var(s)
   | Abs(s, t) -> if x = pos then Abs("x_" ^ pos, (rename_free_var t s ("x_" ^ pos)))
                       else Abs(s, rename_position_r t x (pos ^ "1"))
   | App(t, u) -> if x = pos then failwith ("error: cannot rename @")
                  else App(rename_position_r t x (pos ^ "1"), rename_position_r u x (pos ^ "2"))
   | LApp(t, u) -> if x = pos then failwith ("error: cannot rename @")
                 else LApp(rename_position_r t x (pos ^ "1"), rename_position_r u x (pos ^ "2"))
   | UApp(t, u) -> if x = pos then failwith ("error: cannot rename _@")
                  else UApp(rename_position_r t x (pos ^ "1"), rename_position_r u x (pos ^ "2"))

let rename_position term x =
 rename_position_r term x "e"

let rec rename_positions term l =
  match l with
  | [] -> term
  | x :: xs -> rename_positions (rename_position term x) xs

let rec erasing_term term =
  match term with
    | Var(s) -> false
    | Abs(s, t) -> if contains (free_variables t) s
                   then erasing_term t else true
    | App(t, u) -> erasing_term t || erasing_term u
    | LApp(t, u) -> erasing_term t || erasing_term u
    | UApp(t, u) -> erasing_term t || erasing_term u

let rec lift term =
  match term with
    | Var(s) -> Var(s)
    | Abs(s, t) -> Abs(s, lift t)
    | App(t, u) -> App(lift t, lift u)
    | LApp(t, u) -> failwith ("error: wrong term syntax")
    | UApp(Abs(s, t), u) -> UApp(Abs(s, (LApp(Var(s), lift t))), lift u)
    | UApp(_, _) -> failwith ("error: wrong term syntax")

let rec project term =
  match term with
    | Var(s) -> Var(s)
    | Abs(s, t) -> Abs(s, project t)
    | App(t, u) -> App(project t, project u)
    | LApp(t, u) -> project u
    | UApp(Abs(s, t), u) -> UApp(Abs(s, project t), project u)
    | UApp(_, _) -> failwith ("error: wrong term syntax")

let rec flatten_fst_r l acc =
 match l with
 | [] -> acc
 | []::xs -> flatten_fst_r xs acc
 | [(x, y)]::xs -> flatten_fst_r xs (x::acc)
 | x::xs -> failwith ("error: not more than one capturing edge")

let flatten_fst l =
 flatten_fst_r l []

let rec fix_term term =
  if alpha_free term then term
  else rename_positions term (flatten_fst (check_paths (term_paths term)))

let rec substitute x t e = match e with
  | Var y -> if (x = y) then t else e
  | Abs(y,t') ->
    if (x = y) then e
    else
    if (not (L.mem y (free_variables t))) then
      Abs(y,(substitute x t t'))
    else if (not (L.mem x (free_variables t'))) then
      Abs(y,t')
    else
      failwith ("error: " ^ y ^ " would be captured by substitution")
  | App(t1,t2) -> App((substitute x t t1), (substitute x t t2))
  | LApp(t1,t2) -> LApp((substitute x t t1), (substitute x t t2))
  | UApp(t1,t2) -> UApp((substitute x t t1), (substitute x t t2))

let beta = function
  | UApp(Abs(x,e1),e2) -> substitute x e2 e1
  | _ -> failwith "can't beta reduce"

let rec normal_form t = match t with
  | UApp(Abs(x,e1),e2) -> normal_form (beta t)
  | UApp(_,e2) -> failwith "wrong term syntax"
  | App(s,t) -> App(normal_form s, normal_form t)
  | LApp(s,t) -> LApp(normal_form s, normal_form t)
  | Abs(x,t) -> Abs(x, normal_form t)
  | Var x -> Var x

let rec map_l_pos_to_u_pos_r l_term l_pos pos u_pos =
  match l_term with
    | Var(s) -> if l_pos = pos then u_pos
                else ""
    | Abs(s, t) -> if l_pos = pos then u_pos
                   else map_l_pos_to_u_pos_r t l_pos (pos ^ "1") (u_pos ^ "1")
    | App(t, u) -> if l_pos = pos then u_pos
                   else (map_l_pos_to_u_pos_r t l_pos (pos ^ "1") (u_pos ^ "1")) ^
                        (map_l_pos_to_u_pos_r u l_pos (pos ^ "2") (u_pos ^ "2"))
    | LApp(t, u) -> (map_l_pos_to_u_pos_r u l_pos (pos ^ "2") u_pos)
    | UApp(t, u) -> if l_pos = pos then u_pos
                   else (map_l_pos_to_u_pos_r t l_pos (pos ^ "1") (u_pos ^ "1")) ^
                        (map_l_pos_to_u_pos_r u l_pos (pos ^ "2") (u_pos ^ "2"))

let rec map_l_pos_to_u_pos l_term l_pos =
  map_l_pos_to_u_pos_r l_term l_pos "e" "e"

let rec fix_u_term term =
  if alpha_free (lift term) then term
  else rename_positions term
    (List.map (map_l_pos_to_u_pos (lift term))
    (uniq (flatten_fst (check_paths (term_paths (lift term))))))

let rec default_names_r term pos =
  match term with
    | Var(s) -> Var(s)
    | Abs(s, t) -> Abs("x_" ^ pos, default_names_r (rename_free_var t s ("x_" ^ pos)) (pos ^ "1"))
    | App(t, u) -> App(default_names_r t (pos ^ "1"), default_names_r u (pos ^ "2"))
    | LApp(t, u) -> LApp(default_names_r t (pos ^ "1"), default_names_r u (pos ^ "2"))
    | UApp(t, u) -> UApp(default_names_r t (pos ^ "1"), default_names_r u (pos ^ "2"))

let default_names term =
  default_names_r term "e"

let alpha_eq t1 t2 =
 default_names t1 = default_names t2

let theorem_ term =
 if alpha_free (lift term) then
   (normal_form term) = project (normal_form (lift term))
 else alpha_eq (normal_form (fix_u_term term))
       (project (normal_form (fix_term (lift term))))


(* Example Terms *)
let t1 = abs "w" (uapp (abs "z" (abs "x" (app (var "z") (var "x")))) (var "z"));;
let t2 = abs "w" (uapp (abs "z" (abs "z" (app (var "z") (var "x")))) (var "z"));;
let t3 = abs "w" (uapp (abs "z" (abs "x" (app (var "z") (var "x")))) (var "x"));;

(* erasing term *)
let t4 = uapp (abs "x" (abs "z" (app (var "x") (var "z")))) (uapp (abs "y" (var "q")) (app (var "x") (var "z")));;

(* term where one capturing edge has to be ignored *)
let t5 = uapp (abs "x" (abs "z" (app (var "x") (var "z")))) (uapp (abs "y" (var "y")) (app (var "x") (var "z")));;

(* term with two capturing edges*)
let t6 = uapp (abs "y" (abs "x" (app (var "y") (var "x"))))
         (uapp (abs "z" (abs "y" (app (var "x") (var "z")))) (var "y")) ;;

let t7 = uapp (abs "x" (abs "z" (app (var "x") (var "z")))) (uapp (abs "y" (abs "x" (var "x"))) (app (var "x") (var "z")));;
let t8 = uapp (abs"y" (abs "x" (var "x"))) (app (var "x") (var "z"));;
let t9 = uapp (abs "x" (uapp (abs "y" (app (var "x") (var "y"))) (var "x"))) (var "y");;
let t10 = uapp (abs "x" (abs "z" (app (var "x") (var "z")))) (uapp (abs "y" (var "y")) (app (var "x") (var "z")));;

(* DOT *)

let rec path_to_dot_str = function
  | [] -> ""
  | (_, y) :: [] -> y
  | (_, y) :: xs -> y ^ " -> " ^ (path_to_dot_str xs)

let rec paths_to_dot_str = function
  | [] -> ""
  | x :: xs -> (path_to_dot_str x) ^ "\n" ^ (paths_to_dot_str xs)

let rec term_nodes_r term pos =
  match term with
  | Var(s) -> [(pos, V(s))]
  | Abs(s, t) -> (pos, L(s)) :: (term_nodes_r t (pos ^ "1"))
  | App(t, u) -> (pos, A("@")) :: ((term_nodes_r t (pos ^ "1")) @ (term_nodes_r u (pos ^ "2")))
  | LApp(t, u) -> (pos, LA("@'")) :: ((term_nodes_r t (pos ^ "1")) @ (term_nodes_r u (pos ^ "2")))
  | UApp(t, u) -> (pos, UA("_@")) :: ((term_nodes_r t (pos ^ "1")) @ (term_nodes_r u (pos ^ "2")))

let term_nodes term =
  term_nodes_r term "e"

let rec term_edges_r term pos =
  match term with
  | Var(s) -> []
  | Abs(s, t) -> (pos, (pos ^ "1")) :: (term_edges_r t (pos ^ "1"))
  | App(t, u) -> (pos, (pos ^ "1")) :: ((pos, (pos ^ "2"))
                  :: ((term_edges_r t (pos ^ "1")) @ (term_edges_r u (pos ^ "2"))))
  | LApp(t, u) -> (pos, (pos ^ "1")) :: ((pos, (pos ^ "2"))
                  :: ((term_edges_r t (pos ^ "1")) @ (term_edges_r u (pos ^ "2"))))
  | UApp(t, u) -> (pos, (pos ^ "1")) :: ((pos, (pos ^ "2"))
                  :: ((term_edges_r t (pos ^ "1")) @ (term_edges_r u (pos ^ "2"))))

let term_edges term =
  term_edges_r term "e"

let rec edges_to_dot = function
  | [] -> ""
  | (p1, p2) :: xs -> (p1 ^ " -> " ^ p2 ^ " [arrowhead=none]; ")
      ^ (edges_to_dot xs)

let rec b_edges_to_dot = function
  | [] -> ""
  | (p1, p2) :: xs -> (p1 ^ " -> " ^ p2 ^ " [color=blue, style=dashed]; ")
      ^ (b_edges_to_dot xs)

let rec c_edges_to_dot = function
  | [] -> ""
  | (p1, p2) :: xs -> (p1 ^ " -> " ^ p2 ^ " [color=red, constraint=false]; ")
      ^ (c_edges_to_dot xs)

let rec path_to_dot = function
  | [] -> ""
  | p1 :: [] -> ""
  | p1 :: (p2 :: xs) -> (p1 ^ " -> " ^ p2 ^ " [arrowhead=none, color=white]; ")
      ^ (path_to_dot (p2 :: xs))

let rec paths_to_dot = function
  | [] -> ""
  | x :: xs -> (path_to_dot x) ^ (paths_to_dot xs)

let node_to_dot pos s fontcolor =
  (pos ^ " [label=<" ^ s ^ "<br/><font point-size=\"10\" color=\"gray40\">" ^ pos
    ^ "</font>>, shape=none, fontcolor=\"" ^ fontcolor ^ "\", fontsize=16]; ")

let rec nodes_to_dot = function
  | [] -> ""
  | (pos, LA(s)) :: xs -> (node_to_dot pos s "green3") ^ (nodes_to_dot xs)
  | (pos, UA(s)) :: xs -> (node_to_dot pos s "red") ^ (nodes_to_dot xs)
  | (pos, A(s)) :: xs -> (node_to_dot pos s "black") ^ (nodes_to_dot xs)
  | (pos, L(s)) :: xs -> (node_to_dot pos ("λ" ^ s) "black") ^ (nodes_to_dot xs)
  | (pos, V(s)) :: xs -> (node_to_dot pos s "black") ^ (nodes_to_dot xs)


let term_to_dot term name =
 "digraph " ^ name ^ " { layout=dot; rankdir=TB; " ^ (nodes_to_dot (term_nodes term)) ^
                       (edges_to_dot (term_edges term)) ^
                       (c_edges_to_dot (t_uniq (List.flatten (check_paths (term_paths term))))) ^
                       (b_edges_to_dot (t_uniq (binding_edges term))) ^ "}"

let export_term_dot term dir name =
  let oc = open_out (dir ^ name ^ ".dot") in
    fprintf oc "%s\n" (term_to_dot term name);
    close_out oc

let export_terms_dot term dir prefix =
  export_term_dot term dir prefix;
  export_term_dot (fix_u_term term) dir (prefix ^ "_fixed");
  export_term_dot (lift term) dir (prefix ^ "_lifted");
  export_term_dot (fix_term (lift term)) dir (prefix ^ "_fixed_lifted");
  export_term_dot (normal_form (fix_term (lift term))) dir (prefix ^ "_nf_fixed_lifted");
  export_term_dot (project (normal_form (fix_term (lift term)))) dir (prefix ^ "_projected_nf_fixed_lifted");
  export_term_dot (project (fix_term (lift term))) dir (prefix ^ "_projected_fixed_lifted");
  export_term_dot (normal_form (fix_u_term term)) dir (prefix ^ "_fixed_nf");
  export_term_dot (normal_form (project (fix_term (lift term)))) dir (prefix ^ "_nf_projected_fixed_lifted");;
