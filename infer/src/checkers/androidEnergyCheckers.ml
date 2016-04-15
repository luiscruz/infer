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
(*not used *)
let proc_iter_all_overridden_methods f tenv proc_name =
  let do_super_type tenv super_class =

		match (PatternMatch.type_get_class_name super_class) with
		| Some mangled_class_name -> (
	    match super_class with
			| Sil.Tstruct({ Sil.def_methods }) ->
	        let is_override pname =
						Procname.get_method pname = Procname.get_method proc_name &&
	          (* Procname.equal pname super_proc_name && *)
	          not (Procname.is_constructor pname) in
	        IList.iter
	          (fun pname ->
	             if is_override pname
	             then f pname)
	          def_methods
	    | _ -> ()
		)
		|  _ -> () in
  match proc_name with
  | Procname.Java proc_name_java ->
      let type_name =
        let class_name = Procname.java_get_class_name proc_name_java in
        Typename.TN_csu (Csu.Class Csu.Java, Mangled.from_string class_name) in
      (match Tenv.lookup tenv type_name with
       | Some curr_struct_typ ->
           Sil.TypSet.iter
             (do_super_type tenv)
             (AndroidFramework.get_all_supertypes (Sil.Tstruct curr_struct_typ) tenv)
       | None ->
           ())
  | _ ->
      ()

let get_procname_struct_typ tenv proc_name= 
	match proc_name with
	| Procname.Java proc_name_java ->
		let type_name =
		  let class_name = Procname.java_get_class_name proc_name_java
			in
		  Typename.TN_csu (Csu.Class Csu.Java, Mangled.from_string class_name)
		in
		(Tenv.lookup tenv type_name)
	| _ -> None	
	
	
let struct_typ_is_super_method_of_pname struct_typ java_pname=
	(*comparison between pnames must ignore class name *)
	IList.fold_left (fun acc e -> acc || ((Procname.java_get_method java_pname) = (Procname.get_method e))) false struct_typ.Sil.def_methods
	
let struct_typ_get_def_method_by_name struct_typ method_name = 
	IList.find (fun def_method -> (method_name = (Procname.get_method def_method))) struct_typ.Sil.def_methods
	
let get_struct_typ_of_typename tenv typename=
	Tenv.lookup tenv typename

let get_overriden_method tenv java_pname=
	let rec get_overriden_method_in_superclasses java_pname superclasses=
		match superclasses with
		| superclass::superclasses_tail -> (
			match get_struct_typ_of_typename tenv superclass with
			| Some struct_typ -> 
				if struct_typ_is_super_method_of_pname struct_typ java_pname then
					Some (struct_typ_get_def_method_by_name struct_typ (Procname.java_get_method java_pname))
				else
					(get_overriden_method_in_superclasses java_pname (superclasses_tail@struct_typ.superclasses))
			| None -> get_overriden_method_in_superclasses java_pname superclasses_tail
		)
		| [] -> None
	in
	match (Tenv.proc_extract_declaring_class_typ tenv java_pname) with
	| Some proc_struct_typ ->
		(get_overriden_method_in_superclasses java_pname proc_struct_typ.superclasses)
	| _ -> None
				
let callback_check_static_method_candidates { Callbacks.proc_desc; proc_name; get_proc_desc; idenv; tenv } =
		let procname_has_class procname classname = match procname with
		| Procname.Java pn_java -> (Procname.java_get_class_name pn_java) = classname
		| _ -> false
		in
		let struct_fields_include struct_fields fieldname =
			match struct_fields with
			| (x_fieldname,_,_)::t when x_fieldname = fieldname -> true
			| _ -> false
		in
		
	  let rec is_static_candidate_do_exp  exp = 
			if Sil.exp_is_this exp then
				false
			else match exp with
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
			| _ -> true
		in
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
					| Sil.Call(_, Sil.Const (Sil.Cfun ((Java pn_java)as pn)), ((_arg1_exp,arg1_typ)::_ as args), loc, _) ->  (* TODO: skip override methods *)
						let arg1_exp = Idenv.expand_expr idenv _arg1_exp in
						let arg1_class =  match (PatternMatch.type_get_class_name arg1_typ) with
							| Some mangled_class_name -> Mangled.to_string mangled_class_name
							| _ -> ""
						in
						not (
							(Sil.exp_is_this arg1_exp) && (* also skips static method calls - they never have _this_*)
							(
								(arg1_class = (Procname.java_get_class_name pn_java)) ||
								(PatternMatch.type_has_direct_supertype arg1_typ (Typename.Java.from_string (Procname.java_get_class_name pn_java))) 
							)
						)
					| _ -> true)
	    | Sil.Nullify _
	    | Sil.Abstract _
	    | Sil.Remove_temps _
	    | Sil.Stackop _
	    | Sil.Declare_locals _ ->
	        true
			in
      (* let is_override pname = (*Todo: this is not efficient -- fold approach should be used*)
				let proc_is_overriding = ref false
				in
        PatternMatch.proc_iter_overridden_methods (fun _ -> proc_is_overriding:=true) tenv pname;
				!proc_is_overriding
			in *)
      let pname_is_overriden tenv pname = (*Todo: this is not efficient -- fold approach should be used*)
				match pname with
				| Procname.Java java_pname ->(
					match get_overriden_method tenv java_pname with
						| Some _ -> true
						| None -> false
				)
				| _ -> false
			in
			let procname_get_overrides tenv proc_name =
				match get_procname_struct_typ tenv proc_name with
				| Some struct_typ -> (Prover.get_overrides_of tenv (Sil.Tstruct(struct_typ)) proc_name)
				| _ -> []
			in
		if not (Procname.java_is_static proc_name) &&
			(not (pname_is_overriden tenv proc_name)) &&
			(IList.length (procname_get_overrides tenv proc_name) = 0)
		then			
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