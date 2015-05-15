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

module I = LustreIdent
module D = LustreIndex
module E = LustreExpr
module N = LustreNode
module S = LustreSlicing
module A = Analyis

module SVS = StateVar.StateVarSet


(* Transition system and information needed when calling it *)
type node_def =

  { 

    (* Node the transition system was created from *)
    node : LustreNode.t;

    (* Initial state predicate *)
    init_uf_symbol : UfSymbol.t;

    (* Transition relation predicate *)
    trans_uf_symbol : UfSymbol.t;

    (* Stateful local variables to be instantiated by the caller 

       Local variables of the callees of the node *)
    lifted_locals : StateVar.t list;

    (* Properties to be instantiated by the caller 

       Properties of the callees of the node *)
    lifted_props : (StateVar.t * TermLib.prop_source) list;

  }


(* Instantiate state variable to the scope of a different node *)
let lift_state_var state_var_map state_var = 

  try 

    (* Find state variable in map *)
    List.find
      (fun (sv, _) -> 
         StateVar.equal_state_vars state_var sv) 
      state_var_map
    |> snd 

  (* Fail, because we don't want a term with state
     variables of mixed scopes *)
  with Not_found -> 

    raise
      (Invalid_argument
         (Format.asprintf 
            "lift_term: state variable %a not found in map"
            StateVar.pp_print_state_var state_var))


(* Instantiate the variables of the term to the scope of a different
   node *)
let lift_term state_var_map term = 

  Term.map

    (function _ -> function 

       (* Need to instantiate free variables *)
       | term when Term.is_free_var term -> 

         (* Get variable of term, this will not fail *)
         let var = Term.free_var_of_term term in

         (* Only if variable is an instance of a state variable *)
         if Var.is_state_var_instance var then 

           (* Get state variable of free variable *)
           let state_var = Var.state_var_of_state_var_instance var in

           (* Get offset of variable instance *) 
           let offset = Var.offset_of_state_var_instance var in

           (* Lift state variable to scope of calling node *)
           let state_var' = lift_state_var state_var_map state_var in


           (* Return state variable instance of the lifted state
              variable at the same offset *)
           Term.mk_var (Var.mk_state_var_instance state_var' offset)

         else

           (* No change if free variable is not an instance of a state
              variable *)
           term

       (* No change term that are not free variables *)
       | term -> term)

    term


(* Lift the name of a property in a subnode by adding the position of
   the node call *)
let lift_prop_name node_name pos prop_name =

  (* Pretty-print a file position *)
  let pp_print_file ppf pos_file = 

    if pos_file = "" then () else
      Format.fprintf ppf "%s" pos_file

  in

  (* Pretty-print a position as attributes *)
  let pp_print_pos ppf pos = 

    (* Do not print anything for a dummy position *)
    if is_dummy_pos pos then () else 

      (* Get file, line and column of position *)
      let pos_file, pos_lnum, pos_cnum = 
        file_row_col_of_pos pos
      in

      (* Print attributes *)
      Format.fprintf 
        ppf
        "[%al%dc%d]"
        pp_print_file pos_file
        pos_lnum
        pos_cnum
  in


  string_of_t
    (fun ppf prop_name ->
       Format.fprintf
         ppf
         "%a%a.%s"
         (LustreIdent.pp_print_ident true) node_name
         pp_print_pos pos
         prop_name)
    prop_name


let call_terms_of_node_call
    mk_fresh_state_var 
    { N.call_node_name; 
      N.call_pos;
      N.call_inputs; 
      N.call_oracles; 
      N.call_outputs } 
    node_locals
    node_props
    { init_uf_symbol;
      trans_uf_symbol;
      node = { N.first_tick;
               N.contract_all_req; 
               N.contract_all_ens; 
               N.inputs;
               N.oracles;
               N.outputs;
               N.locals; 
               N.props } as node;
      lifted_locals; 
      lifted_props } =

  (* Initialize map of state variable in callee to instantiated state
     variable in caller *)
  let state_var_map = 

    (* Inputs *)
    D.fold2
      (fun _ state_var inst_state_var state_var_map -> 
         (state_var, inst_state_var) :: state_var_map)
      inputs
      call_inputs
      []

    |> 

    (* Outputs *)
    D.fold2
      (fun _ state_var inst_state_var state_var_map -> 
         (state_var, inst_state_var) :: state_var_map)
      outputs
      call_outputs

  |> (fun state_var_map ->
       
       (* Oracles *)
       List.fold_left2 
         (fun state_var_map state_var inst_state_var -> 
            (state_var, inst_state_var) :: state_var_map)
         state_var_map
         oracles
         call_oracles)

  in

  (* Create fresh state variable for each state variable local
     to the called node and add to the respective data
     structures *)
  let node_locals, call_locals, state_var_map = 

    List.fold_left

      (fun (locals, call_locals, state_var_map) state_var -> 

         (* Instantiate state variable to a fresh state
            variable *)
         let inst_state_var = 
           mk_fresh_state_var
             ?is_const:(Some (StateVar.is_const state_var))
             ?for_inv_gen:(Some true)
             (StateVar.type_of_state_var state_var)
         in

         (* Add fresh state variable to state variables of this
            node, to actual input parameters of node call and to
            map of state variable instances *)
         (inst_state_var :: locals,
          inst_state_var :: call_locals,
          (state_var, inst_state_var) :: state_var_map))

      (node_locals, [], [])
      (List.fold_left
         (fun a e -> D.values e @ a) 
         (first_tick :: lifted_locals)
         locals)

  in

  (* Instantiate all properties of the called node in this node *)
  let node_props = 
    List.fold_left 
      (fun a (sv, n, src) -> 

         ((* Lift state variable 
             
             Property is a local variable, thus it has been
             instantiated and is in the map *)
           lift_state_var state_var_map sv,
             
           (* Lift name of property *)
           lift_prop_name call_node_name call_pos n,
           
           (* Property is instantiated *)
           TermLib.Instantiated
             ([I.string_of_ident false call_node_name], n)) :: a)

      node_props
      props 

  in

  (* Add requirements of node as property if any *)
  let node_props = if N.has_contract node then 

      (lift_state_var state_var_map contract_all_req,
       lift_prop_name call_node_name call_pos "requirement",
       TermLib.Requirement
         (call_pos, [I.string_of_ident false call_node_name], []))
      :: node_props

    else

      node_props

  in

  let init_call_of_bound term_of_state_var =
    List.map 
      term_of_state_var
      (lift_state_var state_var_map first_tick :: 
       (D.values call_inputs) @ 
       (D.values call_outputs) @
       call_locals)

    |> Term.mk_uf init_uf_symbol

  in
    

  let init_call_term =
    init_call_of_bound
      (E.base_term_of_state_var TransSys.init_base)
  in

  let init_call_term_trans = 
    init_call_of_bound
      (E.cur_term_of_state_var TransSys.trans_base)
  in
        
  let trans_call_term =
    List.map 
      (E.cur_term_of_state_var TransSys.trans_base)
      (lift_state_var state_var_map first_tick :: 
       (List.filter 
          (fun sv -> StateVar.is_const sv |> not) 
          (D.values call_inputs)) @ 
       D.values call_outputs @
       call_locals)

    |> Term.mk_uf trans_uf_symbol

  in

  state_var_map, 
  node_locals, 
  node_props, 
  call_locals,
  init_call_term_trans, 
  init_call_term, 
  trans_call_term
  

let rec definitions_of_node_calls 
    mk_fresh_state_var
    trans_sys_defs
    node_locals
    node_props 
    init_terms
    trans_terms = 

  function

    (* Definitions for all node calls created, return *)
    | [] -> (node_locals, node_props, init_terms, trans_terms)

    (* Node call without an activation condition *)
    | { N.call_node_name; N.call_clock = None } as node_call :: tl -> 

      (try 

         (* Get additional information about transition system of a
            callee *)
         let node_trans_sys =
           List.assoc call_node_name trans_sys_defs 
         in

         let state_var_map, node_locals, node_props, _, init_term, _, trans_term =
           call_terms_of_node_call
             mk_fresh_state_var
             node_call
             node_locals
             node_props
             node_trans_sys
         in

         definitions_of_node_calls 
           mk_fresh_state_var
           trans_sys_defs
           node_locals
           node_props
           (init_term :: init_terms)
           (trans_term :: trans_terms)
           tl

       with Not_found -> assert false)


    (* Condact node call *)
    | { N.call_node_name; 
        N.call_clock = Some clock;
        N.call_inputs;
        N.call_outputs; 
        N.call_defaults } as node_call :: tl -> 

      (try 

         (* Get additional information about transition system of a
            callee *)
         let { node = { N.first_tick; N.inputs }} as node_trans_sys =
           List.assoc call_node_name trans_sys_defs 
         in

         (* Create shadow variable for each non-constant input *)
         let 

           (* Add shadow state variable to local variables, return
              term at previous instant, equation with corresponding
              inputs, and equation with previous state value *)
           (local_vars,
            propagate_inputs_init, 
            propagate_inputs_trans, 
            interpolate_inputs) =

           D.fold2
             (fun
               _ 
               formal_sv 
               actual_sv
               (local_vars, 
                propagate_inputs_init, 
                propagate_inputs_trans, 
                interpolate_inputs) ->

               (* Skip over constant formal inputs *)
               if StateVar.is_const formal_sv then 

                 (local_vars, 
                  propagate_inputs_init, 
                  propagate_inputs_trans, 
                  interpolate_inputs )

               else

                 (* Create fresh shadow variable for input *)
                 let shadow_sv = 
                   mk_fresh_state_var
                     ?is_const:None
                     ?for_inv_gen:(Some false)
                     (StateVar.type_of_state_var formal_sv) 
                 in

                 (* Shadow variable takes value of input *)
                 let p_i = 
                   Term.mk_eq
                     [E.base_term_of_state_var TransSys.init_base actual_sv; 
                      E.base_term_of_state_var TransSys.init_base shadow_sv]
                 in

                 (* Shadow variable takes value of input *)
                 let p_t = 
                   Term.mk_eq
                     [E.cur_term_of_state_var TransSys.trans_base actual_sv; 
                      E.cur_term_of_state_var TransSys.trans_base shadow_sv]
                 in

                 (* Shadow variable takes its previous value *)
                 let i = 
                   Term.mk_eq
                     [E.cur_term_of_state_var TransSys.trans_base shadow_sv; 
                      E.pre_term_of_state_var TransSys.trans_base shadow_sv]
                 in

                 (* Add shadow variable and equations to accumulator *)
                 (shadow_sv :: local_vars,
                  p_i :: propagate_inputs_init, 
                  p_t :: propagate_inputs_trans, 
                  i :: interpolate_inputs))

             inputs
             call_inputs

             (node_locals, [], [], [])

         in


         let 

           state_var_map, 
           node_locals, 
           node_props, 
           call_locals,
           init_term, 
           init_term_trans, 
           trans_term =

           call_terms_of_node_call
             mk_fresh_state_var
             { node_call with N.call_inputs = call_inputs }
             node_locals
             node_props
             node_trans_sys
         in

         let clock_init = 
           E.base_term_of_state_var TransSys.init_base clock 
         in

         let clock_trans = 
           E.cur_term_of_state_var TransSys.init_base clock 
         in

         let first_tick_trans = 
           lift_state_var state_var_map first_tick
           |> E.cur_term_of_state_var TransSys.init_base 
         in

         let init_term = 

           Term.mk_and 

             [

               (* Propagate input values to shadow variables on clock
                  tick *)
               Term.mk_implies 
                 [clock_init;
                  Term.mk_and propagate_inputs_init];

               (* Initial state constraint on clock tick *)
               Term.mk_implies [clock_init; init_term];

               (* Defaults on no clock tick *)
               Term.mk_implies 
                 [Term.mk_not clock_init;
                  Term.mk_and
                    (D.fold2
                       (fun _ sv { E.expr_init } accum ->
                          Term.mk_eq 
                            [E.base_term_of_state_var TransSys.init_base sv;
                             E.base_term_of_expr TransSys.init_base expr_init] :: 
                          accum)
                       call_outputs
                       call_defaults
                       [])]

             ]

         in

         let trans_term =
           Term.mk_and
             [

               (* Propagate input values to shadow variables on clock
                  tick *)
               Term.mk_implies 
                 [clock_trans;
                  Term.mk_and propagate_inputs_trans];

               (* Interpolate input values in shadow variable between
                  clock ticks *)
               Term.mk_implies 
                 [Term.mk_not clock_trans; Term.mk_and interpolate_inputs];

               (* Transition relation with true activation condition
                    on the first clock tick *)
               Term.mk_implies
                 [Term.mk_and 
                    [clock_trans; first_tick_trans];
                  init_term_trans];

               (* Transition relation with true activation condition
                  on following clock ticks *)
               Term.mk_implies
                 [Term.mk_and
                    [clock_trans; Term.mk_not first_tick_trans];
                  trans_term];

               (* Transition relation with false activation
                  condition *)
               Term.mk_implies 
                 [Term.mk_not clock_trans;
                  Term.mk_and 
                    (List.fold_left
                       (fun accum state_var ->
                          Term.mk_eq 
                            [E.cur_term_of_state_var
                               TransSys.trans_base 
                               state_var; 
                             E.pre_term_of_state_var
                               TransSys.trans_base
                               state_var] :: 
                          accum)
                       []
                       call_locals
                     |> D.fold
                          (fun _ state_var accum -> 
                           Term.mk_eq 
                             [E.cur_term_of_state_var
                                TransSys.trans_base 
                                state_var; 
                              E.pre_term_of_state_var
                                TransSys.trans_base
                                state_var] :: 
                           accum)
                          call_outputs) ]

             ]

         in

         definitions_of_node_calls
           mk_fresh_state_var
           trans_sys_defs
           node_locals
           node_props
           (init_term :: init_terms)
           (trans_term :: trans_terms)
           tl

       with Not_found -> assert false)


let rec definitions_of_asserts
    init_terms
    trans_terms = 

  function

    (* All assertions consumed, return term for initial state
       constraint and transition relation *)
    | [] -> (init_terms, trans_terms)
            
    (* Assertion with term for initial state and term for transitions *)
    | { E.expr_init; E.expr_step } as expr :: tl ->

       (* Term for assertion in initial state *)
       let init_term =
         E.base_term_of_expr TransSys.init_base expr_init
       in 

       (* Term for assertion in step state *)
       let trans_term =
         E.cur_term_of_expr TransSys.trans_base expr_step
       in 

       (* Add constraint unless it is true *)
       let init_terms = 
         if Term.equal init_term Term.t_true then
           init_terms
         else
           init_term :: init_terms 
       in

       (* Add constraint unless it is true *)
       let trans_terms = 
         if Term.equal trans_term Term.t_true then
           trans_terms
         else
           trans_term :: trans_terms 
       in

      (* Continue with next assertions *)
      definitions_of_asserts init_terms trans_terms tl
      


let rec definitions_of_equations 
    init
    stateful_vars
    instance
    terms = 

  function 

    (* Constraints for all equations generated *)
    | [] -> terms 

    (* State variable must have an equational constraint *)
    | (state_var, [], { E.expr_init; E.expr_step }) :: tl 
      when List.exists (StateVar.equal_state_vars state_var) stateful_vars -> 

      (* Equation for stateful variable *)
      let def = 

        Term.mk_eq 

          (if init then 

             (* Equation for initial constraint on variable *)
             [E.base_term_of_state_var TransSys.init_base state_var; 
              E.base_term_of_expr TransSys.init_base expr_init] 

           else

             (* Equation for transition relation on variable *)
             [E.cur_term_of_state_var TransSys.trans_base state_var; 
              E.cur_term_of_expr TransSys.trans_base expr_step])

      in

      (* Add terms of equation *)
      definitions_of_equations 
        init
        stateful_vars
        instance
        (def :: terms)
        tl


    (* Can define state variable with a let binding *)
    | (state_var, [], ({ E.expr_init; E.expr_step } as expr)) :: tl ->

      (* Let binding for stateless variable *)
      let def =

        (* Conjunction of previous terms of definitions *)
        (Term.mk_and terms) 

        |>

        (* Define variable with a let *)
        Term.mk_let 

          (if init then 

             (* Binding for the variable at the base instant only *)
             [(E.base_var_of_state_var TransSys.init_base state_var, 
               E.base_term_of_expr TransSys.init_base expr_init)] 

           else

             (* Binding for the variable at the current instant *)
             [(E.cur_var_of_state_var TransSys.trans_base state_var, 
               E.cur_term_of_expr TransSys.trans_base expr_step);

              (* Binding for the variable at the previous instant *)
              (E.pre_var_of_state_var TransSys.trans_base state_var, 
               E.pre_term_of_expr TransSys.trans_base expr_step)])

      in

      (* Start with singleton lists of let-bound terms *)
      definitions_of_equations 
        init
        stateful_vars
        instance
        [def]
        tl

    (* Array state variable *)
    | (state_var, bounds, { E.expr_init; E.expr_step }) :: tl -> 

      (* Return the i-th index variable *)
      let index_var_of_int i = 
        E.mk_index_var i
        |> E.state_var_of_expr
        |> Var.mk_const_state_var
      in

      (* Add quantifier or let binding for indexes of variable *)
      let add_bounds = function 

        (* Fixed index [e] *)
        | N.Fixed e -> 

          (* let bind index variable to value [e] *)
          fun (a, i) ->
            (Term.mk_let 
               [index_var_of_int i,
                (e : E.expr :> Term.t)]
               a,
             pred i)

        (* Variable index of size [e] *)
        | N.Bound e -> 
          fun (a, i) -> 

            (* Index variable *)
            let v = index_var_of_int i in

            (* Qunatify over index variable between 0 and [e] *)
            (Term.mk_forall
               [v]
               (Term.mk_implies 
                  [Term.mk_leq [Term.mk_num Numeral.zero; Term.mk_var v; 
                                (e : E.expr :> Term.t)]; a]),
             pred i)
      in

      (* Uninterpreted function application for array *)
      let uf_term = 
        Term.mk_uf
          (StateVar.uf_symbol_of_state_var state_var)

          ((* First parameter is node instance *)
            (Var.mk_const_state_var instance
             |> Term.mk_var) :: 

            (* Following parameters are indexes *)
            (List.fold_left
               (fun (a, i) _ -> 
                  (index_var_of_int i
                   |> Term.mk_var) :: a,
                  succ i)
               ([], 0)
               bounds 
             |> fst))
      in

      (* Assign value to array position *)
      let eq = 

        Term.mk_eq 

          (uf_term::

           if init then 
             
             (* Expression at base instant *)
             [E.base_term_of_expr TransSys.init_base expr_init]
             
           else
             
             (* Expression at current instant *)
             [E.cur_term_of_expr TransSys.trans_base expr_step])

      in

      (* Wrap equation in let binding and quantifiers for indexes *)
      let def, _ = 
        List.fold_right
          add_bounds
          bounds
          (eq, List.length bounds)
      in

      (* Add definition and continue *)
      definitions_of_equations 
        init
        stateful_vars
        instance
        (def :: terms)
        tl

(*

(* Create definition of initial state predicate *)
let mk_init_def 
    { N.name; N.first_tick; N.running } 
    signature_state_vars 
    init_terms =

  (* Create instances of state variables in signature *)
  let init_signature_vars = 
    List.map 
      (fun sv ->
         Var.mk_state_var_instance sv TransSys.init_base)
      signature_state_vars
  in

  (* Create uninterpreted symbol for initial state predicate *)
  let uf_symbol = 
    UfSymbol.mk_uf_symbol
      (Format.asprintf
         "%s_%a"
         I.init_uf_string
         (LustreIdent.pp_print_ident false) name)
      (List.map Var.type_of_var init_signature_vars)
      Type.t_bool
  in

  (* Definition of initial state predicate *)
  let init_term = 
    Term.mk_and 

      (* Stream first_tick is true *)
      ((Var.mk_state_var_instance first_tick TransSys.init_base
        |> Term.mk_var) ::
       
       (* Stream running is true *)
       (Var.mk_state_var_instance running TransSys.init_base
        |> Term.mk_var) ::
       
       (* Constraints of node *)
       init_terms)

  in

  (* Return definition of initial state predicate *)
  (uf_symbol, (init_signature_vars, init_term))
   
     

(* Create definition of transition relation predicate *)
let mk_trans_def 
    { N.name; N.first_tick; N.running } 
    signature_state_vars 
    trans_terms =

  (* Create instances of state variables in signature *)
  let trans_signature_vars = 

    (* All state variables at the current instant *)
    List.map 
      (fun sv ->
         Var.mk_state_var_instance sv TransSys.trans_base)
      signature_state_vars @

    (* Not constant state variables at the previous instant *)
    List.map 
      (fun sv -> 
         Var.mk_state_var_instance 
           sv
           (TransSys.trans_base |> Numeral.pred))
      (List.filter
         (fun sv -> not (StateVar.is_const sv)) 
         signature_state_vars)
  in

  (* Create uninterpreted symbol for transition relation predicate *)
  let uf_symbol = 
    UfSymbol.mk_uf_symbol
      (Format.asprintf
         "%s_%a"
         I.trans_uf_string
         (LustreIdent.pp_print_ident false) name)
      (List.map Var.type_of_var trans_signature_vars)
      Type.t_bool
  in

  (* Definition of transition relation predicate *)
  let trans_term = 
    Term.mk_and 

      (* Stream first_tick is false *)
      ((Var.mk_state_var_instance first_tick TransSys.trans_base
        |> Term.mk_var
        |> Term.mk_not) ::       
       
       (* Stream running is true *)
       (Var.mk_state_var_instance running TransSys.trans_base
        |> Term.mk_var) ::
       
       (* Constraints of node *)
       trans_terms)

  in

  (* Return definition of transition relation predicate *)
  (uf_symbol, (trans_signature_vars, trans_term))
*)

let rec trans_sys_of_node'
    trans_sys_defs
    output_input_dep_init
    output_input_dep_trans
    nodes_abst
    node_impl
    abst_impl_map =

  function

    (* Transition system for all nodes created *)
    | [] -> 

      (* Return transition system of top node *)
      (match trans_sys_defs with
        | [] -> assert false
        | (_, trans_sys) :: _ -> trans_sys)

    (* Create transition system for top node *)
    | node_name :: tl -> 

      try 

        (* Transition system for node has been created and added to
           accumulator meanwhile? *)
        let trans_sys = List.assoc node_name trans_sys_defs in

        (* Continue with next transition systems *)
        trans_sys_of_node'
          trans_sys_defs
          output_input_dep_init
          output_input_dep_trans
          nodes_abst
          node_impl
          abst_impl_map 
          tl

      (* Transition system has not been created *)
      with Not_found -> 

        (* Is node abstract? *)
        let is_abstr = 

          try 

            (* Find abstraction flag for node in map *)
            List.assoc node_name abst_impl_map

          (* Default to implementation *)
          with Not_found -> false

        in

        (* Node to create a transition system for, sliced to
           abstraction or to implementation *)
        let { N.instance;
              N.first_tick; 
              N.inputs; 
              N.oracles; 
              N.outputs; 
              N.locals; 
              N.equations; 
              N.calls; 
              N.asserts; 
              N.props;
              N.contracts } as node = 

          try 

            (* Find node in abstract or implementation nodes by name *)
            N.node_of_name
              node_name
              (if is_abstr then nodes_abst else node_impl)

          (* Fall back to implementation if no abstraction for node
             exists *)
          with Not_found -> 

            try 

              (* Find node in implementation nodes by name *)
              N.node_of_name node_name node_impl

            with Not_found -> 

              (* Must have at least implementation of node *)
              raise
                (Invalid_argument
                   (Format.asprintf 
                      "trans_sys_of_node: node %a not found"
                      (I.pp_print_ident false) node_name))

        in

        (* Return true if state variable is local to the node *)
        let is_node_local_state_var sv =

          (* State variable is not an oracle *)
          not 
            (List.exists
               (StateVar.equal_state_vars sv)
               oracles) &&

          (* State variable is not an input *)
          not 
            (D.exists
               (fun _ -> StateVar.equal_state_vars sv)
               inputs) &&

          (* State variable is not an output *)
          not 
            (D.exists
               (fun _ -> StateVar.equal_state_vars sv)
               outputs)

        in

        (* Index for fresh state variables *)
        let index_ref = ref 0 in

        (* Create a fresh state variable *)
        let mk_fresh_state_var
            ?is_const
            ?for_inv_gen
            state_var_type =

          (* Increment counter for fresh state variables *)
          incr index_ref; 

          (* Create state variable *)
          StateVar.mk_state_var
            ~is_input:false
            ?is_const:is_const
            ?for_inv_gen:for_inv_gen
            ((I.push_index I.inst_ident !index_ref) 
             |> I.string_of_ident false)
            [(I.string_of_ident false) node_name]
            state_var_type

        in

        (* Subnodes for which we have not created a transition system *)
        let tl' = 

          List.fold_left 
            (fun accum { N.call_node_name } -> 
               if 

                 (* Transition system for node created? *)
                 List.mem_assoc call_node_name trans_sys_defs || 

                 (* Node already pushed to stack? *)
                 List.mem call_node_name accum

               then 

                 (* Continue with stack unchanged *)
                 accum

               else

                 (* Push node to top of stack *)
                 call_node_name :: accum)

            []
            calls

        in

        (* Are there subnodes for which a transition system needs to be
           created first? *)
        match tl' with

          (* Some transitions systems of called nodes have not been
             created *)
          | _ :: _ -> 

            (* TODO: Check here that the call graph does not have
               cycles *)

            (* Recurse to create transition system for subnode, then
               return to this node *)
            trans_sys_of_node'
              trans_sys_defs
              output_input_dep_init
              output_input_dep_trans
                  nodes_abst
              node_impl
              abst_impl_map 
              (tl' @ node_name :: tl)

          (* All transitions systems of called nodes have been
             created *)
          | [] ->

            (* Instantiated state variables and constraints from node
               calls *)
            let locals', props', init_terms, trans_terms = 
              definitions_of_node_calls
                mk_fresh_state_var
                trans_sys_defs
                (List.fold_left (fun a c -> D.values c @ a) [] locals)
                props
                []
                []
                calls 
            in

            (* Stateful state variables in node, including state
               variables for node instance, first tick and running
               flags, and state variables capturing outputs of node
               calls *)
            let stateful_vars = 
              (N.stateful_vars_of_node node 
               |> SVS.elements
               |> List.filter is_node_local_state_var) @ 
              locals' 
            in

            (* State variables in the signature of the predicate in
               the correct order *)
            let signature_vars = 
              instance ::
              first_tick ::
              (D.values inputs) @ 
              oracles @
              (D.values outputs) 
            in

            (* Constraints from assertions

               Must add assertions and contract first so that local variables
               can be let bound in definitions_of_equations *)
            let init_terms, trans_terms = 
              definitions_of_asserts  
                init_terms
                trans_terms
                asserts
            in

            (* Order initial state equations by dependency and
               generate terms *)
            let equations_init, node_output_input_dep_init =

              S.order_equations true output_input_dep_init node

              |>
              
              (fun (e, d) -> 
                 definitions_of_equations
                   true
                   stateful_vars
                   instance
                   init_terms
                   e,
                 
                 d)
            in

            (* Order transition relation equations by dependency and
               generate terms *)
            let equations_init, node_output_input_dep_trans =

              S.order_equations false output_input_dep_trans node

              |>
              
              (fun (e, d) -> 
                 definitions_of_equations
                   false
                   stateful_vars
                   instance
                   trans_terms
                   e,
                 
                 d)
            in

(*
            (* Definition of initial state predicate *)
            let init_def = 
              mk_init_def node signature_vars init_terms
            in

            (* Definition of transition relation predicate *)
            let trans_def = 
              mk_trans_def node signature_vars trans_terms
            in

            let trans_sys = 
              TransSys.mk_trans_sys 
                [I.string_of_ident false node_name]
                []
                init_def
                trans_def
                []
                []
                None
                (TransSys.Lustre [])
            in
*)

            (* Create transition relation *)
            trans_sys_of_node'
              ((node_name,
               { node;
                 init_uf_symbol;
                 trans_uf_symbol;
                 lifted_locals;
                 lifted_props })
               :: trans_sys_defs)
              ((node_name, node_output_input_dep_init) :: 
               output_input_dep_init)
              ((node_name, node_output_input_dep_trans) :: 
               output_input_dep_trans)
              nodes_abst
              node_impl
              abst_impl_map 
              tl
          

let trans_sys_of_nodes nodes = 
  trans_sys_of_node' [] [] [] [] nodes [] [List.hd nodes |> fun { N.name } -> name]



(* 
   Local Variables:
   compile-command: "make -k -C .."
   indent-tabs-mode: nil
   End: 
*)
