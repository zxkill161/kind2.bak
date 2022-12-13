(* This file is part of the Kind 2 model checker.

   Copyright (c) 2015 by the Board of Trustees of the University of Iowa

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
open Actlit

(* Raised when the unrolling alone is unsat (with the bound). *)
exception UnsatUnrollingExc of int

(* Output statistics *)
let print_stats () = 

  KEvent.stat 
    [Stat.misc_stats_title, Stat.misc_stats;
     Stat.bmc_stats_title, Stat.bmc_stats;
     Stat.smt_stats_title, Stat.smt_stats]

(* Clean up before exit *)
let on_exit _ =

  (* Stop all timers. *)
  Stat.bmc_stop_timers ();
  Stat.smt_stop_timers ();

  (* Output statistics *)
  print_stats ()

(* Returns true if the property is not falsified or valid. *)
let shall_keep trans (s,_) =
  match TransSys.get_prop_status trans s with
  | Property.PropInvariant _
  | Property.PropFalse _ -> false
  | _ -> true

(* Check-sat and splits properties.. *)
let split trans solver k to_split actlit =

  (* Function to run if sat. *)
  let if_sat _ =

    (* Get the full model *)
    let model =
      SMTSolver.get_var_values
        solver
        (TransSys.get_state_var_bounds trans)
        (TransSys.vars_of_bounds trans Numeral.zero k)
    in
    
    (* Extract counterexample from model *)
    let cex =
      Model.path_from_model (TransSys.state_vars trans) model k
    in

    (* Evaluation function. *)
    let eval term =
      Eval.eval_term (TransSys.uf_defs trans) model term
      |> Eval.bool_of_value
    in
    (* Splitting properties. *)
    let new_to_split, new_falsifiable =
      List.partition
        ( fun (_, term) ->
          Term.bump_state k term |> eval )
        to_split
    in
    (* Building result. *)
    Some (new_to_split, (new_falsifiable, cex))
  in

  (* Function to run if unsat. *)
  let if_unsat _ =
    None
  in

  Format.asprintf
    "Looking for falsification at %a."
    Numeral.pp_print_numeral k
  |> SMTSolver.trace_comment solver ;

  (* Check sat assuming with actlits. *)
  SMTSolver.check_sat_assuming solver if_sat if_unsat [actlit]

(* Splits its input list of properties between those that can be
   falsified and those that cannot after asserting the actlit
   implications. *)
let split_closure trans solver k to_split =

  let rec loop falsifiable list =
    (* Building negative term. *)
    let term =
      list |> List.map (fun pair -> snd pair)
      |> Term.mk_and |> Term.mk_not |> Term.bump_state k
    in
    (* Getting actlit for it. *)
    let actlit = fresh_actlit () in
    (* Declaring actlit. *)
    actlit |> SMTSolver.declare_fun solver ;
    let actlit = term_of_actlit actlit in
    (* Deactivation function. *)
    let deactivate () =
      actlit |> Term.mk_not |> SMTSolver.assert_term solver
    in
    (* Asserting implication. *)
    Term.mk_implies [ actlit ; term ]
    |> SMTSolver.assert_term solver ;
    (* Splitting. *)
    match split trans solver k list actlit with
    | None ->
      deactivate () ;
      list, falsifiable
    | Some ([], new_falsifiable) ->
      deactivate () ;
       [], new_falsifiable :: falsifiable
    | Some (new_list, new_falsifiable) ->
      deactivate () ;
       loop (new_falsifiable :: falsifiable) new_list
  in

  loop [] to_split

(* Find out which reachability query has the lowest lower bound (for the purpose
   of skipping steps) *)
let lowest_lower_bound trans =
  TransSys.get_properties trans |> 
  List.fold_left (fun num_skip prop -> match (prop.Property.prop_status, prop.Property.prop_kind) with
    (* Ignore finished properties *)
    | (Property.PropInvariant _, _)
    | (Property.PropFalse _, _) -> num_skip
    (* Update lowest lower bound *)
    | (_, Property.Reachable (Some (From b))) 
    | (_, Property.Reachable (Some (At b))) 
    | (_, Property.Reachable (Some (FromWithin (b, _)))) -> if b < num_skip then b else num_skip
    (* Shouldn't be possible, but if there are other types of properties, we shouldn't skip steps *)
    | _ -> 0) max_int 

(*
let re_init trans k =
  let llb = lowest_lower_bound trans in
  let num_skip = llb - Numeral.to_int k in
  num_skip > 0
*)


let skip_steps_next trans solver step k (* nu_unknowns *) = 
  let llb = lowest_lower_bound trans in
    let num_skip = llb - Numeral.to_int k in
    while (Numeral.to_int !step) < (Numeral.to_int k + num_skip) do
      step := Numeral.succ !step;

      (* Declaring unrolled vars at k+1. *)
      TransSys.declare_vars_of_bounds
      trans (SMTSolver.declare_fun solver) !step !step ;

      (* Asserting transition relation for next iteration. *)
      TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) trans !step
      |> SMTSolver.assert_term solver ;

      
      (* Assert all invariants, including new ones, at [k]. *)
      (*let all_invs =
        TransSys.invars_of_bound
          ~one_state_only:Numeral.(equal !step zero) trans !step
        |> Term.mk_and
      in
      if (all_invs != Term.t_true) then
        SMTSolver.assert_term solver all_invs;

      (* Asserting implications if k > 0. *)
      if Numeral.(!step > zero) then
        nu_unknowns
        |> List.map (fun (_, term) -> Term.bump_state Numeral.(!step-one) term)
        |> Term.mk_and |> SMTSolver.assert_term solver *)
        
    done(*;
  let all_invs =
    TransSys.invars_of_bound
      ~one_state_only:Numeral.(equal !step zero) trans !step
    |> Term.mk_and
  in
  if (all_invs != Term.t_true) then
    SMTSolver.assert_term solver all_invs;

  (* Asserting implications if k > 0. *)
  if Numeral.(!step > zero) then
    nu_unknowns
    |> List.map (fun (_, term) -> Term.bump_state Numeral.(!step-one) term)
    |> Term.mk_and |> SMTSolver.assert_term solver *)

(* Performs the next check after updating its context with new
   invariants and falsified properties. Assumes the solver is
   in the following state:

   prop@i
     for all 0 <= i <= k-2 and prop      in 'unknowns';

   invariant@i
     for all 0 <= i <= k and invariant in 'invariants';

   T[i-1,i]
     for all 1 <= i <= k.

   Note that the transition relation for the current iteration is
   already asserted. *)
let rec next (input_sys, aparam, trans, solver, k, unknowns, invs) =
  (* Getting new invariants and updating transition system. *)
  let new_invs =
    (* Receiving messages. *)
    KEvent.recv ()
    (* Updating transition system. *)
    |> KEvent.update_trans_sys input_sys aparam trans
    (* Extracting one- and two-state invariants. *)
    |> fst
  in

  if
    (new_invs |> fst |> Term.TermSet.is_empty |> not) ||
    (new_invs |> snd |> Term.TermSet.is_empty |> not)
  then
    (* Assert new invariants up to [k-1]. *)
    Unroller.assert_new_invs_to solver k new_invs ;

  (* Assert all invariants, including new ones, at [k]. *)
  let all_invs =
    TransSys.invars_of_bound
      ~one_state_only:Numeral.(equal k zero) trans k
    |> Term.mk_and
  in
  if (all_invs != Term.t_true) then
    SMTSolver.assert_term solver all_invs;

  (* Cleaning unknowns by removing invariants and falsifieds. *)
  let nu_unknowns = unknowns |> List.filter (shall_keep trans) in

  match nu_unknowns with
  | [] -> ()

  | _ ->
    let k_int = Numeral.to_int k in

    (* Notifying framework of our progress. *)
    Stat.set k_int Stat.bmc_k ;
    KEvent.progress k_int ;
    Stat.update_time Stat.bmc_total_time ;

    (* Asserting implications if k > 0. *)
    if Numeral.(k > zero) then
      nu_unknowns
      (* If we're skipping steps, we don't need to assert that the property
         held in the previous step *)
      |> List.filter (fun (name, _) -> match TransSys.get_prop_kind trans name with
        | Reachable Some (From b)
        | Reachable Some (At b) 
        | Reachable Some (FromWithin (b, _))-> b < k_int
        | _ -> true
      ) 
      |> List.map (fun (_, term) -> Term.bump_state Numeral.(k-one) term)
      |> Term.mk_and |> SMTSolver.assert_term solver ;

    (* (Temporarily) filter out properties with a lower bound smaller than
       current k. *)
    let out_of_bounds, nu_unknowns = nu_unknowns |> List.partition (
      fun (name,_) -> match TransSys.get_prop_kind trans name with
      | Reachable Some (From b)
      | Reachable Some (At b) 
      | Reachable Some (FromWithin (b, _))-> b > k_int
      | _ -> false
    ) in

    (* Filtering properties which are not known to be k-true at this step. *)
    let unknowns_at_k, k_true =
      nu_unknowns |> List.partition (
        fun (name,_) -> match (TransSys.get_prop_status trans name, TransSys.get_prop_kind trans name) with
        | (Property.PropKTrue k, Invariant) 
        | (Property.PropKTrue k, Reachable None) -> k_int > k
        | (Property.PropKTrue k, Reachable Some (From b)) -> k_int > k && b <= k_int
        | (Property.PropKTrue k, Reachable Some (Within b)) -> k_int > k && b >= k_int
        | (Property.PropKTrue k, Reachable Some (At b)) -> k_int > k && b = k_int
        | (Property.PropKTrue k, Reachable Some (FromWithin (b1, b2))) -> k_int > k && b1 <= k_int && b2 >= k_int
        | _ -> true
      )
    in
    let step = ref k in
    let unfalsifiable =
      match unknowns_at_k with
      | [] ->
        KEvent.log
          L_info
          "BMC @[<v>at k = %i@,\
                    skipping@]"
          k_int ;
        nu_unknowns

      | _ ->
        (* Output current progress. *)
        KEvent.log
          L_info
          "BMC @[<v>at k = %i@,\
                    %i properties.@]"
          k_int (List.length unknowns_at_k) ;

        Format.asprintf
          "%a unrolling satisfiability check."
          Numeral.pp_print_numeral k
        |> SMTSolver.trace_comment solver ;

        (*if re_init trans k then init input_sys aparam trans invs |> next else*)

        (* Function 'skip_steps_next' has the side effect of skipping steps
           for reachability queries if we know we have to unroll the transition
           relation many times before we can find an example trace. *)
        if not invs then skip_steps_next trans solver step k;
        let k = !step in

        if Flags.BmcKind.check_unroll () then ( 
          if SMTSolver.check_sat solver |> not then (
            KEvent.log
              L_warn
              "BMC @[<v>Unrolling of the system is unsat at %a, \
              the system has no more reachable states.@]"
              Numeral.pp_print_numeral k ;
            raise (UnsatUnrollingExc (Numeral.to_int k))
          )
        ) ;

        (* Splitting. *)
        let unfalsifiable, falsifiable =
          split_closure trans solver k unknowns_at_k
        in

        (* The out of bounds properties trivially hold *)
        let unfalsifiable = out_of_bounds @ unfalsifiable in

        (* Broadcasting k-true properties. *)
        unfalsifiable |> List.iter ( fun (s, _) ->
          KEvent.prop_status
            (Property.PropKTrue (Numeral.to_int k))
            input_sys
            aparam
            trans
            s
            (TransSys.property_of_name trans s).prop_kind
        ) ;

        (* Broadcasting falsified properties. *)
        falsifiable |> List.iter ( fun (p, cex) ->
          List.iter
            ( fun (s,_) ->
              KEvent.prop_status
                (Property.PropFalse (Model.path_to_list cex)) 
                input_sys
                aparam
                trans
                s
                (TransSys.property_of_name trans s).prop_kind )
            p
        ) ;

        k_true @ unfalsifiable
    in
    let k = !step in
    (* K plus one. *)
    let k_p_1 = Numeral.succ k in

    (* Declaring unrolled vars at k+1. *)
    TransSys.declare_vars_of_bounds
     trans (SMTSolver.declare_fun solver) k_p_1 k_p_1 ;
     
    (* Asserting transition relation for next iteration. *)
     TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) trans k_p_1
    |> SMTSolver.assert_term solver ;

    (* Output statistics *)
    print_stats ();

    (* Int k plus one. *)
    let k_p_1_int = Numeral.to_int k_p_1 in

    (* Checking if we have reached max k. *)
    if Flags.BmcKind.max () > 0 && k_p_1_int > Flags.BmcKind.max () then
     KEvent.log
       L_info
       "BMC @[<v>reached maximal number of iterations.@]"
    else
     (* Looping. *)
     next
      (input_sys, aparam, trans, solver, k_p_1, unfalsifiable, invs)

        

and skip_steps_init trans solver =
  let num_skip = lowest_lower_bound trans in
  let step = ref Numeral.one in
  while Numeral.to_int !step <= num_skip do
    (* Declaring unrolled vars at k+1. *)
    TransSys.declare_vars_of_bounds
    trans (SMTSolver.declare_fun solver) !step !step ;

    (* Asserting transition relation for next iteration. *)
    TransSys.trans_of_bound (Some (SMTSolver.declare_fun solver)) trans !step
    |> SMTSolver.assert_term solver ;

    step := Numeral.succ !step;
  done;
  num_skip

(* Initializes the solver for the first check. *)
and init input_sys aparam trans invs =
  (* Starting the timer. *)
  Stat.start_timer Stat.bmc_total_time;

  (* Getting properties. 
     Filter for invariants or reachability queries *)
  let unknowns =
    if invs then
      (TransSys.props_list_of_bound_no_skip trans Numeral.zero)
    else
      (TransSys.props_list_of_bound_skip trans Numeral.zero)
  in

  (*let unknowns = TransSys.props_list_of_bound trans Numeral.zero in*)

  (* Creating solver. *)
  let solver =
    SMTSolver.create_instance ~produce_assignments:true
      (TransSys.get_logic trans) (Flags.Smt.solver ())
  in

  (* Defining uf's and declaring variables. *)
  TransSys.define_and_declare_of_bounds
    trans
    (SMTSolver.define_fun solver)
    (SMTSolver.declare_fun solver)
    (SMTSolver.declare_sort solver)
    Numeral.zero Numeral.zero ;

  (* Asserting init. *)
  TransSys.init_of_bound
    (Some (SMTSolver.declare_fun solver)) trans Numeral.zero
  |> SMTSolver.assert_term solver ;

  (* Function 'skip_steps_init' has the side effect of skipping steps
      for reachability queries if we know we have to unroll the transition
      relation many times before we can find an example trace. *)
  let num_skip = if invs then 0 else skip_steps_init trans solver in

  SMTSolver.trace_comment solver "Initial state satisfiability check." ;

  if Flags.BmcKind.check_unroll () then (
    if SMTSolver.check_sat solver |> not then (
      KEvent.log
        L_warn
        "BMC @[<v>Initial state is unsat, the system has no \
         reachable states.@]" ;
      raise (UnsatUnrollingExc 0)
    )
  ) ;

  (* Start "next" at a timestep after Numeral.zero *)
  (input_sys, aparam, trans, solver, Numeral.of_int num_skip, unknowns, invs)

(* Runs the base instance. *)
let main invs input_sys aparam trans =
  try
    init input_sys aparam trans invs |> next
  with UnsatUnrollingExc k ->
    let _, _, unknown = TransSys.get_split_properties trans in
    unknown |> List.iter (fun p ->
        let cert = k, p.Property.prop_term in
        KEvent.prop_status
          (Property.PropInvariant cert)
          input_sys aparam trans p.Property.prop_name p.Property.prop_kind
      )





(* 
   Local Variables:
   compile-command: "make -C .. -k"
   tuareg-interactive-program: "./kind2.top -I ./_build -I ./_build/SExpr"
   indent-tabs-mode: nil
   End: 
*)

