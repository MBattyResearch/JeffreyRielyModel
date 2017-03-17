theory ExampleEventStructuresRelational
imports Enum EventStructuresRelational Relation Transitive_Closure
begin
  
theorem "isValidPO {} {}"
  apply(simp add: isValidPO_def)
  done

theorem "well_justified empty_ES {''a''}"
  apply(auto simp add: well_justified_def isValidES_def empty_ES_def isValidPO_def)
        apply(simp add: trans_def antisym_def symmetric_def refl_on_def)
    defer 1
        apply(rule Relation.trans_Id)
       apply(rule Relation.antisym_Id)
      defer 1
      apply(rule Relation.trans_Id)
     apply(auto simp add: justified_def subset_AE_justifies_def ae_justifies_def justifies_config_def)
  oops

definition jctc6 :: "string event_structure_data" where
"jctc6 \<equiv> \<lparr> 
    event_set = { ''a'', ''b'', ''c'', ''d'', ''e'', ''f'', ''g'', ''h'' },
    primitive_order =  { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') },
    primitive_conflict =  { (''e'', ''g''), (''b'', ''d'') },
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

thm trancl_induct
  
definition po :: "char list \<Rightarrow> char list \<Rightarrow> bool" where
  "po x y \<equiv> (x, y) \<in> ((primitive_order jctc6)\<^sup>*)"

lemma irefl_trancl: "\<forall>r . acyclic r \<longrightarrow> irrefl (r\<^sup>+)"
  by (simp add: acyclic_irrefl)
  
locale program_order =
  fixes po :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
  assumes refl [intro, simp]: "x \<sqsubseteq> x"
    and anti_sym [intro]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> x\<rbrakk> \<Longrightarrow> x = y"
    and trans [trans]: "\<lbrakk>x \<sqsubseteq> y; y \<sqsubseteq> z\<rbrakk> \<Longrightarrow> x \<sqsubseteq> z"

context program_order
begin
  
definition (in program_order) test :: "string \<Rightarrow> string \<Rightarrow> bool"  where
  "test x y \<equiv> (x, y) \<in> { (''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'') }"

lemma "irreflp test"
  apply(simp add: irreflp_def)
  apply(simp add: test_def)
  done
    
lemma "acyclicP test"
  apply(simp add: acyclic_def)
  apply(unfold trancl_unfold_left)
  apply(unfold test_def)
    try
  oops
    
end
    
lemma test_lemma: "\<forall>x. (y, x) \<notin> r \<Longrightarrow> y \<notin> (Domain (r\<^sup>+))"
  apply auto
  done
    
thm "trancl_induct"
  
schematic_goal acyclic_po: "\<nexists>x. (x, x) \<in> {(''a'', ''g''), (''a'', ''e''), (''a'', ''d''), (''a'', ''b''), (''g'', ''h''), (''b'', ''c''), (''e'', ''f'')}\<^sup>+"
  apply(induction rule: trancl_trans_induct)
  apply(unfold trancl_unfold_left)
  oops
    
  (*by (meson acyclic_def irrefl_def trancl_induct)*)
    
thm rtrancl_refl  
value "r = {(0,0)} \<longrightarrow> (r) \<subseteq> (Field r \<times> Field r)"
  
  
theorem trancl_sub_r_cross_r: "\<forall>r . r\<^sup>* \<subseteq> ((Field r) \<times> (Field r))"
  try
  
theorem "isValidPO (event_set jctc6) ((primitive_order jctc6)\<^sup>*)"
  apply(auto simp add: isValidPO_def jctc6_def)
    defer 1
    apply(rule trans_rtrancl)
   apply(rule acyclic_impl_antisym_rtrancl)
   apply(simp add: acyclic_def irrefl_def)
   apply(rule acyclic_po)
  apply(rule refl_onI)
    
    try