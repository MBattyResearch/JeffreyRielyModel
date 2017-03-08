theory EventStructures
imports Main Enum String "~~/src/HOL/Library/FSet"
begin

datatype mem_action = W | R | I 
(*Memory action, location, value*)
datatype label = Label mem_action string int

type_synonym 'a config = "'a set"

(*Prime Event Structure with below restrictions*)
record 'a event_structure_data =
  event_set :: "'a set"
  partial_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  primitive_conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_function :: "'a \<Rightarrow> label"

definition fin :: "'a set \<Rightarrow> bool" where
"fin es \<equiv> finite es"

definition refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"refl po \<equiv> (\<forall>x. po x x)"

definition trans :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"trans po \<equiv> (\<forall>x.\<forall>y.\<forall>z. (po x y \<and> po y z) \<longrightarrow> po x z)"

definition antisym :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"antisym po \<equiv> (\<forall>x.\<forall>y. (po x y \<and> po y x) \<longrightarrow> x = y)"

definition isValidPO :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isValidPO po \<equiv> (
  refl po \<and> 
  trans po \<and> 
  antisym po
)"

definition symmetric :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"symmetric conf \<equiv> (\<forall>x.\<forall>y. conf x y \<longrightarrow> conf y x)" 

definition isConfValid :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isConfValid conf \<equiv> (
  symmetric conf \<and> 
  trans conf
)"

definition confOverPO :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"confOverPO po conf \<equiv> (\<forall>x.\<forall>y.\<forall>z. (conf x y \<and> po y z) \<longrightarrow> conf x z)"

(*Minimal/Primitive conflict condition*)
definition minimal :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"minimal po conf \<equiv> 
  (\<forall>w.\<forall>x.\<forall>y.\<forall>z. (conf y z \<and> po x y \<and> conf x w \<and> po w z \<longrightarrow> (y = x) \<and> (w = z)))"

definition isValid :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a set  \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isValid po es conf \<equiv> (
  finite es \<and>
  isValidPO po \<and>
  minimal po conf \<and> 
  isConfValid conf
)"

declare isValid_def [simp]
declare minimal_def [simp]
declare isConfValid_def [simp]


(*written own reflexive transitive closure for reasons*)
inductive transitive_closure :: "('a  \<Rightarrow> 'a  \<Rightarrow> bool) \<Rightarrow> 'a  \<Rightarrow> 'a  \<Rightarrow> bool" for r where
refl: "transitive_closure r x x "|
step: "r x y \<Longrightarrow> transitive_closure r y z \<Longrightarrow> transitive_closure r x z"

lemma transitive_closure_t: "\<lbrakk>transitive_closure r x y; transitive_closure r y z\<rbrakk> \<Longrightarrow> transitive_closure r x z"
  apply(induction rule: transitive_closure.induct)
   apply(assumption)
  apply(metis step)
  done
    
(* no idea.
inductive antisymmetric :: "('a  \<Rightarrow> 'a  \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
base: "antisymmetric r x y \<Longrightarrow> \<not>(r y x) \<Longrightarrow> (x \<equiv> y)" |
step: "r x y \<Longrightarrow> antisymmetric r x y" 
*)

(*symmetric transitive closure (not reflexive) *)
inductive symmetric_transitive_closure :: "('a  \<Rightarrow> 'a  \<Rightarrow> bool) \<Rightarrow> 'a  \<Rightarrow> 'a  \<Rightarrow> bool" for r where
symm: "symmetric_transitive_closure r x y \<and> x \<noteq> y \<Longrightarrow> symmetric_transitive_closure r y x" |
step: "r x y \<Longrightarrow> symmetric_transitive_closure r y z \<Longrightarrow> symmetric_transitive_closure r x z"

definition isValidES :: "'a event_structure_data \<Rightarrow> bool" where
"isValidES es == isValid 
  (transitive_closure (partial_order es))
  (event_set es)
  (symmetric_transitive_closure (primitive_conflict es))" 

fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I '''' v) (Label R l2 v2) = (v2 = 0)"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
"justifies_event x (Label W l v) = True"|
"justifies_event x (Label I l v) = True"|
"justifies_event x y = False"

(*
record 'a configuration = 
  event_set :: "'a set"
  order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_fn :: "'a \<Rightarrow> label"*)

definition conflict_free :: "'a config \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"conflict_free c conf \<equiv> (\<forall>e\<in>c. \<not>(\<exists>f\<in>c. conf e f))"

(*Helper function to get the type of memory action from an event label*)
fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label I l v) = I"|
"getMemAction (Label W l v) = W"|
"getMemAction (Label R l v) = R"

(*is this correct?*)
definition down_closure :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> bool" where
"down_closure events order labelfn \<equiv> (\<forall>e\<in>events. \<exists>f\<in>events. 
  (order f e) \<or> ((getMemAction (labelfn e)) = I))"

(*All read events in a configuration are justified by an event in that configuration*)
definition justified :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> bool" where
"justified es c \<equiv>
   (\<forall>r\<in> c. (getMemAction (label_function es r) = R) \<longrightarrow> (\<exists>e\<in>c. (justifies_event (label_function es e) (label_function es r))))"

(*for all events in event structure 1 there exists an event in event structure 2 that justifies it*)
definition justifies_config :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
"justifies_config es c1 c2 \<equiv>
   (\<forall>x\<in>c2. \<exists>y\<in>c1. (justifies_event (label_function es y) (label_function es x)))"

(*
definition justified_config_reln :: "('a event_structure_data \<times> 'a event_structure_data) set" where
"justified_config_reln \<equiv> { (e1, e2) . justifies_config e1 e2 }"
*)


(*event structure 1 AE (always eventually) justifies event structure 2*)
definition ae_justifies :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
"ae_justifies es c1 c2 \<equiv> 
  \<forall>x.(transitive_closure (justifies_config es) c1 x) \<longrightarrow> (\<exists>y.(transitive_closure (justifies_config es) x y) \<and> (justifies_config es y c2))"

definition empty_ES :: "'a event_structure_data" where
"empty_ES \<equiv> 
  \<lparr> event_set = {},
  partial_order = \<lambda>x y. False,
  primitive_conflict = \<lambda>x y. False,
  label_function = \<lambda>x.(Label I '''' 0) \<rparr>"

(*True at configuration level*)
definition is_subseteq :: "'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
"is_subseteq c1 c2 \<equiv>  c1 \<subseteq> c2"

definition subset_AE_justifies :: "'a event_structure_data \<Rightarrow> 'a config \<Rightarrow> 'a config \<Rightarrow> bool" where
"subset_AE_justifies es c1 c2 \<equiv> (is_subseteq c1 c2) \<and> (ae_justifies es c1 c2)"

definition well_justified :: "'a event_structure_data \<Rightarrow> 'a config  \<Rightarrow> bool" where
"well_justified es c \<equiv> (isValidES es) \<and> (justified es c) \<and> (transitive_closure (subset_AE_justifies es) (event_set empty_ES) c)"

end