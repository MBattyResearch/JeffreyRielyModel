theory jctc6
imports EventStructures String
begin

definition jctc6 :: "string event_structure" where
"jctc6 \<equiv> \<lparr> 
    event_set = { ''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''g'', ''h'' },
    primitive_order =  { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') },
    primitive_conflict = { (''e'', ''g''), (''b'', ''d'') },
    label_function = \<lambda>x.
        if x = ''b'' then Label R ''A'' 1 (* r1 *)
        else if x = ''c'' then Label W ''B'' 1
        else if x = ''d'' then Label R ''A'' 0 (* r1 *)
        else if x = ''e'' then Label R ''B'' 1 (* r2 *)
        else if x = ''f'' then Label W ''A'' 1
        else if x = ''g'' then Label R ''B'' 0 (* r2 *)
        else if x = ''h'' then Label W ''A'' 1
        else Label I '''' 0
\<rparr>"


definition jctc6_expected_results :: "string set set" where 
"jctc6_expected_results = { {''b'', ''e''} }"

  
 (* play with this is fine, don't keep (finite d). Use locale instead. *)
function tc_fun:: "'a set  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"tc_fun d r x z = ((finite d) \<longrightarrow> (\<exists>y . y \<in> d \<longrightarrow> ((r x z) \<or> (r x y \<and> tc_fun (d - {y}) r y z))))"
by pat_completeness auto
termination tc_fun
  apply(relation "measure (\<lambda>(d,_,_,_) . (card d))")
   apply(simp_all)
  using Finite_Set.card_Suc_Diff1 by fastforce

fun domain_fun:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set" where
"domain_fun r =  { x . (\<exists> y. r x y \<or> r y x) }"

lemma acy: "acyclic (primitive_order jctc6)"
  apply(simp add: jctc6_def)
  apply(auto)
        apply(simp add: acyclic_def)
       apply(rule rtrancl.cases, auto)+
  done

theorem "isValidPO (event_set jctc6) ((primitive_order jctc6)\<^sup>*)"
  apply(auto simp add: isValidPO_def jctc6_def)
    apply(rule refl_rtrancl)
    apply(rule trans_rtrancl)
  apply(rule acyclic_impl_antisym_rtrancl)
  apply(simp add: acy)
  apply auto
    apply(simp add: acyclic_def)
        apply(rule rtrancl.cases, auto)+
  done
