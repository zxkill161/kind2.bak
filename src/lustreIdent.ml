(* This file is part of the Kind 2 model checker.

   Copyright (c) 2014 by the Board of Trustees of the University of Iowa

   Licensed under the Apache License, Version 2.0 (the "License"); you
   may not use this file except in compliance with the License.  You
   may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0 

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
   implied. See the License for the specific language governing
   permissions and limitations under the License. 

*)

open Lib

(* ********************************************************************** *)
(* Types                                                                  *)
(* ********************************************************************** *)

(* An index of an identifier 

   Leave this as IntIndex of int, so that we have a concrete type that
   the polymorphic comparison and equality functions apply to. This
   makes it easier to use association lists. 
*)
type one_index = 

  (* String as index *)
  | StringIndex of string

  (* Integer as index *)
  | IntIndex of int

  (* Variable as index *)
  | VarIndex 


(* A list of indexes *)
type index = one_index list


(* The empty index *)
let empty_index = []


(* An identifier *)
type t = string * index


(* Comparision of indexes: *)
let compare_one_index a b = match a, b with 

  (* Compare strings *)
  | StringIndex a, StringIndex b -> Pervasives.compare a b

  (* Compare integers *)
  | IntIndex a, IntIndex b -> compare a b

  (* Compare variables

     Do implicit alpha conversion, two variables are equal *)
  | VarIndex, VarIndex -> 0

  (* String indexes are greater than integer indexes *)
  | StringIndex _, IntIndex _ -> 1 

  (* String indexes are greater than variable indexes *)
  | StringIndex _, VarIndex -> 1 

  (* Integer indexes are greater than variable indexes *)
  | IntIndex _, VarIndex -> 1 

  (* Integer indexes are smaller than string indexes *)
  | IntIndex _, StringIndex _ -> -1 

  (* Variable  indexes are smaller than string indexes *)
  | VarIndex, StringIndex _ -> -1 

  (* Variable indexes are smaller than integer indexes *)
  | VarIndex, IntIndex _ -> -1 


(* Lexicographic comparison of lists of indexes *)
let rec compare_index a b = match a, b with 

  (* Lists are equal *)
  | [], [] -> 0

  (* Longer list is greater *)
  | _, [] -> 1 

  (* Shorter list is smaller *)
  | [], _ -> -1 

  (* Compare head elements of lists *)
  | a :: atl, b :: btl -> match compare_one_index a b with 
    
    (* Head elements are equal, recurse to compare tails *)
    | 0 -> compare_index atl btl 
             
    (* Return comparison of head elements *)
    | c -> c 


(* Set of identifiers *)  
module LustreIndexSet = Set.Make 
    (struct 
      type t = index
      let compare = compare_index
    end)


(* Map of indexes *)  
module LustreIndexMap = Map.Make 
    (struct 
      type t = index
      let compare = compare_index
    end)


(* Map of single indexes *)  
module LustreOneIndexMap = Map.Make 
    (struct 
      type t = one_index
      let compare = compare_one_index
    end)


(* Trie of idexes *)  
module LustreIndexTrie = Trie.Make (LustreOneIndexMap)


(* Trie of indexed indentifiers *)
module LustreIdentTrie = struct

  (* Convert identifier to index by using name as first index *)
  let index_of_ident (s, i) = StringIndex s :: i

  (* Convert index to identifier by taking first index as name *)
  let ident_of_index = function 
    | StringIndex s :: i -> (s, i) 
    | _ -> assert false

  (* A key is an indexed identifier *)
  type key = t

  (* The trie is actually a trie over indexes *)
  type 'a t = 'a LustreIndexTrie.t

  (* Delegate to trie module *)
  let empty = LustreIndexTrie.empty

  (* Delegate to trie module *)
  let is_empty = LustreIndexTrie.is_empty

  (* Convert identifier to indexes before querying *)
  let mem k = LustreIndexTrie.mem (index_of_ident k)

  (* Convert identifier to indexes before adding *)
  let add k = LustreIndexTrie.add (index_of_ident k)

  (* Convert identifier to indexes before removing *)
  let remove k = LustreIndexTrie.remove (index_of_ident k)

  (* Delegate to trie module *)
  let compare = LustreIndexTrie.compare

  (* Delegate to trie module *)
  let equal = LustreIndexTrie.equal

  (* Convert indexes to identifier before evaluating function *)
  let iter f = LustreIndexTrie.iter (function k -> f (ident_of_index k))

  (* Convert indexes to identifier before evaluating function *)
  let fold f = LustreIndexTrie.fold (function k -> f (ident_of_index k))

  (* Convert indexes to identifier before evaluating function *)
  let for_all p = LustreIndexTrie.for_all (function k -> p (ident_of_index k))

  (* Convert indexes to identifier before evaluating function *)
  let exists p = LustreIndexTrie.exists (function k -> p (ident_of_index k))

  (* Return trie with only bindings that satisfy the predicate *)
  let filter p = LustreIndexTrie.filter (function k -> p (ident_of_index k))

  (* Convert indexes to identifier before returning *)
  let bindings t = 
    LustreIndexTrie.fold 
      (fun k v a -> ((ident_of_index k), v) :: a)
      t
      []

  let max_binding t = 
    let k, v = LustreIndexTrie.max_binding t in
    (ident_of_index k, v)

  let min_binding t = 
    let k, v = LustreIndexTrie.min_binding t in
    (ident_of_index k, v)

  let cardinal = LustreIndexTrie.cardinal

  (* Convert identifier to indexes before querying *)
  let find k = LustreIndexTrie.find (index_of_ident k)

  (* Convert identifier to indexes before querying *)
  (* Delegate to trie module *)
  let map = LustreIndexTrie.map

  (* Convert indexes to identifier before evaluating function *)
  let mapi f = LustreIndexTrie.mapi (function k -> f (ident_of_index k))

  let find_prefix k = LustreIndexTrie.find_prefix  (index_of_ident k)

  (* Convert a subtrie of a trie of identifiers to a map of its indexes *)
  let to_map t  = 
    LustreIndexTrie.fold LustreIndexMap.add t LustreIndexMap.empty 

  let iter2 f = 
    LustreIndexTrie.iter2 (fun k v1 v2 -> f (ident_of_index k) v1 v2)

  let map2 f = 
    LustreIndexTrie.map2 
       (fun k v1 v2 -> f (ident_of_index k) v1 v2)

  let fold2 f = 
    LustreIndexTrie.fold2 
       (fun k v1 v2 a -> f (ident_of_index k) v1 v2 a)

  let values = LustreIndexTrie.values

  let keys t = 
    LustreIndexTrie.fold 
      (fun k _ a -> (ident_of_index k) :: a)
      t
      []

end




(* Compare indexed identifiers *)
let compare (a, ia)  (b, ib) = 

  (* Compare strings *)
  match compare a b with 

    (* Strings are equal, compare indexes *)
    | 0 -> compare_index ia ib

    (* Return comparison of strings *)
    | c -> c
  

(* Equality on indexed identifiers *)
let equal i1 i2 = compare i1 i2 = 0


(* Set of identifiers *)  
module LustreIdentSet = Set.Make 
    (struct 
      type z = t
      type t = z
      let compare = compare
    end)

(* Map of identifiers *)  
module LustreIdentMap = Map.Make 
    (struct 
      type z = t
      type t = z
      let compare = compare
    end)


(* ********************************************************************** *)
(* Pretty-printers                                                        *)
(* ********************************************************************** *)


(* Pretty-print an index *)
let pp_print_one_index' db = function 
  
  | false -> 
    
    (function ppf -> function 
       | StringIndex i -> Format.fprintf ppf ".%s" i
       | IntIndex i -> Format.fprintf ppf "[%d]" i
       | VarIndex -> Format.fprintf ppf "X%d" db)

  | true -> 
    
    (function ppf -> function 
       | StringIndex i -> Format.fprintf ppf "_%s" i
       | IntIndex i -> Format.fprintf ppf "_%d" i
       | VarIndex -> Format.fprintf ppf "_x%d" db)

(* Pretty-print an index with variable at index 0 *)
let pp_print_one_index safe ppf index = 
  pp_print_one_index' 0 safe ppf index

(* Pretty-print a list of indexes *)
let rec pp_print_index' db safe ppf = function 
  | [] -> ()
  | h :: tl -> 
    pp_print_one_index' db safe ppf h; 
    pp_print_index' (succ db) safe ppf tl

(* Pretty-print a list of indexes with variable index at starting 0 *)
let pp_print_index safe ppf index = pp_print_index' 0 safe ppf index

(* Pretty-print an identifier *)
let rec pp_print_ident safe ppf (s, i) = 

  Format.fprintf ppf "%s%a" s (pp_print_index safe) i


(* Return a string representation of an identifier *)
let string_of_ident safe = string_of_t (pp_print_ident safe)


(* Construct an identifier of a string *)
let mk_string_ident string = (string, empty_index)


(* Construct an identifier of a string *)
let mk_string_one_index string = StringIndex string


(* Construct an identifier of a string *)
let mk_string_index string = [mk_string_one_index string]


(* Construct an identifier of a string *)
let mk_int_one_index num = IntIndex (Numeral.to_int num)


(* Construct an identifier of a string *)
let mk_int_index num = [mk_int_one_index num]



(* Push the index as an element index to the given index *)
let push_one_index_to_index index1 index2 = index1 :: index2

let push_back_one_index_to_index index1 index2 = index2 @ [index1]


(* Push the string as an element index to the given index *)
let push_string_index_to_index string index = StringIndex string :: index 

let push_back_string_index_to_index string index = index @ [StringIndex string]


(* Push the integer as an element index to the given index *)
let push_int_index_to_index int index = 
  IntIndex (Numeral.to_int int) :: index 

let push_back_int_index_to_index int index = 
  index @ [IntIndex (Numeral.to_int int)]


(* Push the identifier as an element index to the given index *)
let push_ident_index_to_index (base_ident, index1) index2 = 

  StringIndex base_ident :: index1 @ index2

let push_back_ident_index_to_index (base_ident, index1) index2 = 

  index2 @ (StringIndex base_ident :: index1)


(* Push the index as an element index to the given index *)
let push_index_to_index index1 index2 = index1 @ index2

let push_back_index_to_index index1 index2 = index2 @ index1


let push_string_index string (base, index) = 
  (base, push_string_index_to_index string index)


let push_back_string_index string (base, index) = 
  (base, push_back_string_index_to_index string index)


let push_int_index int (base, index) = 
  (base, push_int_index_to_index int index)

let push_back_int_index int (base, index) = 
  (base, push_back_int_index_to_index int index)


let push_ident_index ident (base, index) = 
  (base, push_ident_index_to_index ident index)

let push_back_ident_index ident (base, index) = 
  (base, push_back_ident_index_to_index ident index)


let push_one_index one_index (base, index) = 
  (base, push_one_index_to_index one_index index)

let push_back_one_index one_index (base, index) = 
  (base, push_back_one_index_to_index one_index index)


let push_index index1 (base, index2) = 
  (base, push_index_to_index index1 index2)

let push_back_index index1 (base, index2) = 
  (base, push_back_index_to_index index1 index2)


(* Construct an index of an identifier *)
let index_of_ident (base, index) = push_string_index base index


let split_ident (base, index) = ((base, empty_index), index)

let split_index index = index

let index_of_one_index_list one_index_list = one_index_list 

(* ********************************************************************** *)
(* Constructors                                                           *)
(* ********************************************************************** *)


(* Construct an index of an identifier *)
let one_index_of_ident = function 
  | (s, []) -> StringIndex s
  | _ -> raise (Invalid_argument "one_index_of_ident")

(* Construct an index of an identifier *)
let index_of_ident (s, i) = StringIndex s :: i


(* Construct an index of an integer *)
let index_of_int i = [IntIndex i]


(* Add a string as an index to an identifier *)
let add_string_index (s, i) j = (s, i @ [StringIndex j])


(* Add an integer as an index to an identifier *)
let add_int_index (s, i) j = (s, i @ [IntIndex j])


let add_ident_index (s, i) = function
  | (j, []) -> (s, i @ [StringIndex j])
  | _ -> raise (Invalid_argument ("Cannot add indexed identifier as index"))

let add_index (s, i) j = (s, i @ j)


let add_int_to_index i j = i @ [IntIndex j]

  

(* ********************************************************************** *)
(* Utility functions                                                      *)
(* ********************************************************************** *)


(* Return a list of strings for index *)
let scope_of_index index =

  List.map 
    (function 
      | StringIndex i -> i
      | IntIndex i -> string_of_int i
      | VarIndex -> raise (Invalid_argument "scope_of_index"))
    index

(* Return a list of strings for indexed identifier *)
let scope_of_ident (ident, index) = ident :: (scope_of_index index)


(* Reserved identifiers *)
let index_ident_string =  "__index" 

let abs_ident_string =  "__abs" 
let oracle_ident_string =  "__nondet" 
let observer_ident_string =  "__observer" 
let ticked_ident_string =  "__ticked" 
let init_uf_string = "__node_init"
let trans_uf_string = "__node_trans"

let top_scope_string = "__top"


(* Return true if the identifier clashes with internal identifier names *)
let ident_is_reserved ident = 

  (* Get string part of identifier *)
  let ident_string, _ : t :> string * _ = ident in

  (* Return false if identical to any reserved identifier *)
  string_starts_with ident_string index_ident_string
  || string_starts_with ident_string abs_ident_string
  || string_starts_with ident_string oracle_ident_string
  || string_starts_with ident_string observer_ident_string
  || string_starts_with ident_string ticked_ident_string
  || string_starts_with ident_string init_uf_string
  || string_starts_with ident_string trans_uf_string
  || string_starts_with ident_string top_scope_string
  

(* Identifier for new variables from abstrations *)
let index_ident = mk_string_ident index_ident_string

(* Identifier for new variables from abstrations *)
let abs_ident = mk_string_ident abs_ident_string

(* Identifier for new oracle input *)
let oracle_ident = mk_string_ident oracle_ident_string

(* Identifier for new oracle input *)
let observer_ident = mk_string_ident observer_ident_string

(* Identifier for new clock initialization flag *)
let ticked_ident = mk_string_ident ticked_ident_string

(* Scope for top-level variables *)
let top_scope_index = mk_string_index top_scope_string



(* 
   Local Variables:
   compile-command: "make -k"
   indent-tabs-mode: nil
   End: 
*)
  
