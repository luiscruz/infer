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
