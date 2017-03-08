theory jctc6
imports EventStructures String "~~/src/HOL/Library/FSet"
begin

definition jctc6 :: "string event_structure_data" where
"jctc6 \<equiv> \<lparr> 
    event_set = { ''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''g'', ''h'' },
    partial_order =  \<lambda>x y. (x,y) \<in> { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') },
    primitive_conflict =  \<lambda>x y. (x,y) \<in> { (''e'', ''g''), (''b'', ''d'') },
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

value "\<forall> V \<in> event_set jctc6 . 
  \<exists> e \<in>event_set jctc6 . justifies_event (label_function jctc6 e) (label_function jctc6 V)"

lemma trans_is_reflexive: "\<forall>r. refl (transitive_closure r)"
  apply(simp add:EventStructures.refl_def transitive_closure.refl)
  done

    (* Mark pines for an infix \in operator, *)
   
lemma r_in_trans:"\<forall>r.\<forall>x.\<forall>y. r x y \<longrightarrow> (transitive_closure r) x y"
  apply(simp add:transitive_closure.step transitive_closure.refl)
  done

lemma trans_trans_r: "\<forall>r. trans (transitive_closure r)"
  apply(auto simp add:EventStructures.trans_def)
  apply(rule transitive_closure_t)
  apply(auto)
  done

  
definition acyc:: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "acyc r \<equiv> \<forall>x y. transitive_closure r x y \<longrightarrow> transitive_closure r y x \<longrightarrow> x = y"
 
(*for all events in event structure 1 there exists an event in event structure 2 that justifies it*)
definition justifies_config :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
"justifies_config es c1 c2 \<equiv>
   (\<forall>x\<in>c2. \<exists>y\<in>c1. (justifies_event (label_function es y) (label_function es x)))"

fun map:: "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b set" where
  "map l f =
    case l of
    | (x::xs) \<Rightarrow> (f x)
    | [] \<Rightarrow> []"

    (* Probably need to remove y from d in the subgoal *)
fun tc_fun:: "'a fset  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
"tc_fun d r x z = (\<exists>y\<in>d . (r x z) \<or> (tc_fun (d - y) r x y \<and> tc_fun (d - y) r y z))"

lemma antisymm_acyclic_r_trans: "\<forall>r . (acyc r) \<longrightarrow> antisym (transitive_closure r)"
  apply(auto simp add:acyc_def)
  apply(simp add: antisym_def)
  done

definition "x \<equiv> (transitive_closure (partial_order jctc6))"
  
theorem acyc_jctc6: "acyc (partial_order jctc6)"
  apply(simp add:acyc_def)
  apply(rule transitive_closure.cases transitive_closure.intros(1) transitive_closure.refl)
    apply(induction rule: transitive_closure.refl)
   apply(simp add: jctc6_def)
    sorry
 
    
  
theorem jctc6_validPO: "isValidPO (transitive_closure (partial_order jctc6))"
  apply(auto simp add:isValidPO_def)
    apply(auto simp add:EventStructures.refl_def)
    apply(simp add: transitive_closure.refl)
   apply(auto simp add: EventStructures.trans_def)
   apply(rule transitive_closure_t)
    apply(simp)
   apply(auto simp add: EventStructures.antisym_def)
  apply (meson acyc_def acyc_jctc6)
  done
    
theorem "isValidES jctc6"
  apply(simp add:isValidES_def jctc6_validPO)
  oops


theorem "\<forall> exp \<in> jctc6_expected_results .
  \<exists> cand_Config . (exp \<subseteq> cand_Config) \<and> (well_justified jctc6 cand_Config)"
  oops
    
   
