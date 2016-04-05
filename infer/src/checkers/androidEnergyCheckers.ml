(*
 * Copyright (c) 2016 - present Luis Cruz.
 *)

let callback_check_internal_acessors { Callbacks.proc_desc; proc_name;get_proc_desc; idenv } =
  let do_instr node = function
    | Sil.Call (_, Sil.Const (Sil.Cfun ((Java pn_java)as pn)), ((_arg1_exp,arg1_typ)::_ as args), loc, _) ->
			let arg1_exp = Idenv.expand_expr idenv _arg1_exp in
			let arg1_class =  match (PatternMatch.type_get_class_name arg1_typ) with
				| Some mangled_class_name -> Mangled.to_string mangled_class_name
				| _ -> "" 
			in
			let proc_get_number_of_nodes = function
				| Some callee_proc_desc -> 
					(IList.length (Cfg.Procdesc.get_nodes callee_proc_desc))
				| _ -> 0
			in
			let proc_desc_get_number_of_sets some_proc_desc= 
				let instr_is_set = function
					| Sil.Set(_,_,_,loc) -> true
					| _ -> false
				in
				match some_proc_desc with
					| Some callee_proc_desc -> 
						Cfg.Procdesc.fold_instrs (fun acc _ instr -> if instr_is_set instr then 1+acc else acc) 0 callee_proc_desc
					| _ -> 0
			in
			if  
				Sil.exp_is_this arg1_exp
				&& (
					(((PatternMatch.is_getter pn_java) && ((IList.length args) = 1)) && (proc_get_number_of_nodes (get_proc_desc pn) = 4) && (proc_desc_get_number_of_sets (get_proc_desc pn) = 1))
					|| (((PatternMatch.is_setter pn_java )&& ((IList.length args) = 2)) && (proc_get_number_of_nodes (get_proc_desc pn) = 5) && (proc_desc_get_number_of_sets (get_proc_desc pn) = 1))
				)
				&& (arg1_class = (Procname.java_get_class_name pn_java))
			then
        let description =
          Printf.sprintf "call to internal accessor method %s" (Procname.java_get_method pn_java) in
        Checkers.ST.report_error
          proc_name
          proc_desc
          "CHECKERS_ANDROID_INTERNAL_ACCESSORS"
          loc
          description
				else
					()
    | _ -> () in
  Cfg.Procdesc.iter_instrs do_instr proc_desc
module L = Logging

				
let callback_check_static_method_candidates { Callbacks.proc_desc; proc_name;get_proc_desc; idenv } =
		let procname_has_class procname classname = match procname with
		| Procname.Java pn_java -> (Procname.java_get_class_name pn_java) = classname
		| _ -> false
		in
		let struct_fields_include struct_fields fieldname =
			match struct_fields with
			| (x_fieldname,_,_)::t when x_fieldname = fieldname -> true
			| _ -> false
		in
		
	  let rec is_static_candidate_do_exp  = function
	    | Sil.Var _ -> true
	    | Sil.UnOp (_, e, _) ->
	        is_static_candidate_do_exp  e
	    | Sil.BinOp (_, e1, e2) ->
	        is_static_candidate_do_exp  e1 &&
	        is_static_candidate_do_exp  e2
	    | Sil.Const _ -> true
	    | Sil.Cast (_, e) ->
	        is_static_candidate_do_exp  e
	    | Sil.Lvar _ -> true
	    | Sil.Lfield (e, fn, Tstruct({struct_name=struct_name_option;static_fields;_})) ->
				let struct_name_string = match struct_name_option with
				| Some struct_name -> Mangled.to_string struct_name
				| _ -> ""
				in
	      if (not (Ident.java_fieldname_is_outer_instance fn)) 
					&& (procname_has_class proc_name struct_name_string)
				  && (not (struct_fields_include static_fields fn)) then
						false
				else is_static_candidate_do_exp e
	    | Sil.Lindex (e1, e2) ->
	        is_static_candidate_do_exp e1 &&
	        is_static_candidate_do_exp e2
	    | Sil.Sizeof _ -> true
			| _ -> true in
	  let instr_is_static = function
	    | Sil.Letderef (_, e, _, _) ->
	        is_static_candidate_do_exp e
	    | Sil.Set (e1, _, e2, _) ->
	        is_static_candidate_do_exp e1 &&
	        is_static_candidate_do_exp e2
	    | Sil.Prune (e, _, _, _) ->
	        is_static_candidate_do_exp e
	    | Sil.Call (_, e, etl, _, _) as function_call_instruction ->
	        is_static_candidate_do_exp e &&
	        IList.fold_left (fun acc (e, _) -> acc &&(is_static_candidate_do_exp e)) true etl &&
					(match function_call_instruction with
					| Sil.Call(_, Sil.Const (Sil.Cfun ((Java pn_java)as pn)), ((_arg1_exp,arg1_typ)::_ as args), loc, _) -> 
						let arg1_exp = Idenv.expand_expr idenv _arg1_exp in
						let arg1_class =  match (PatternMatch.type_get_class_name arg1_typ) with
							| Some mangled_class_name -> Mangled.to_string mangled_class_name
							| _ -> ""
						in
						not (
							(Sil.exp_is_this arg1_exp) && (* also skips static method calls - they never have _this_*)
							(arg1_class = (Procname.java_get_class_name pn_java))
						)
					| _ -> true)
	    | Sil.Nullify _
	    | Sil.Abstract _
	    | Sil.Remove_temps _
	    | Sil.Stackop _
	    | Sil.Declare_locals _
	    | Sil.Goto_node _ ->
	        true in
		if not (Procname.java_is_static proc_name) then			
			let method_should_be_static = 
				Cfg.Procdesc.fold_instrs (fun acc _ instr -> (acc && (instr_is_static instr))) true proc_desc
			in
		  if method_should_be_static then
		  	let loc = Cfg.Procdesc.get_loc proc_desc in
	      Checkers.ST.report_error
	        proc_name
	        proc_desc
	        "CHECKERS_ANDROID_SHOULD_BE_STATIC"
	        loc
	        "should be static"