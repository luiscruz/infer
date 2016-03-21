(*
 * Copyright (c) 2016 - present Luis Cruz.
 *)

let callback_check_internal_acessors { Callbacks.proc_desc; proc_name; idenv } =
  let do_instr node = function
    | Sil.Call (_, Sil.Const (Sil.Cfun (Java pn)), ((_arg1_exp,arg1_typ)::_ as args), loc, _) ->
			let arg1_exp = Idenv.expand_expr idenv _arg1_exp in
			let arg1_class =  match (PatternMatch.type_get_class_name arg1_typ) with
				| Some mangled_class_name -> Mangled.to_string mangled_class_name
				| _ -> "" 
			in
			if  
				Sil.exp_is_this arg1_exp
				&& (((PatternMatch.is_getter pn) && ((IList.length args) = 1)) || (PatternMatch.is_setter pn && ((IList.length args) = 2)) )
				&& (arg1_class = (Procname.java_get_class_name pn) )
			then
        let description =
          Printf.sprintf "call to internal accessor method %s" (Procname.java_get_method pn) in
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
