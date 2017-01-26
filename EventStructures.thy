theory EventStructures
imports Main Enum String 
begin

datatype mem_action = W | R | I 
datatype label = Label mem_action string int

(*Prime Event Structure with below restrictions*)
record 'a event_structure_data =
  event_set :: "'a set"
  partial_order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  primitive_conflict :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_function :: "'a \<Rightarrow> label"

definition refl :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"refl po \<equiv> (\<forall>x. po x x \<longrightarrow> True)"

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

definition isValid :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"isValid po conf \<equiv> (
  minimal po conf \<and> 
  confOverPO po conf \<and> 
  isConfValid conf \<and> 
  isValidPO po
)"

definition isValidES :: "'a event_structure_data \<Rightarrow> bool" where
"isValidES es == isValid (partial_order es) (primitive_conflict es)" 

fun justifies_event :: "label \<Rightarrow> label \<Rightarrow> bool" where
"justifies_event (Label I l v) (Label R l2 v2) = ((l = l2) \<and> (v = 0))"|
"justifies_event (Label W l v) (Label R l2 v2) = ((l = l2) \<and> (v = v2))"|
"justifies_event x y = False"

(*
record 'a configuration = 
  event_set :: "'a set"
  order :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  label_fn :: "'a \<Rightarrow> label"*)

definition conflict_free :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"conflict_free events conf \<equiv> (\<forall>e\<in>events. \<not>(\<exists>f\<in>events. conf e f))"

fun getMemAction :: "label \<Rightarrow> mem_action" where
"getMemAction (Label I l v) = I"|
"getMemAction (Label W l v) = W"|
"getMemAction (Label R l v) = R"

(*is this correct?*)
definition down_closure :: "'a set \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> label) \<Rightarrow> bool" where
"down_closure events order labelfn \<equiv> (\<forall>e\<in>events. \<exists>f\<in>events. 
  (order f e) \<or> ((getMemAction (labelfn e)) = I))"

(*All read events re justified by an event in an event structure*)
definition justified :: "'a event_structure_data \<Rightarrow> bool" where
"justified es  \<equiv>
   (\<forall>r\<in>(event_set es). \<exists>e\<in>(event_set es). (getMemAction (label_function es r) = R) \<and> (justifies_event (label_function es e) (label_function es r)))"

(*for all events in event structure 1 there exists an event in event structure 2 that justifies them*)
definition justifies_config :: "'a event_structure_data \<Rightarrow> 'a event_structure_data \<Rightarrow> bool" where
"justifies_config es1 es2 \<equiv>
   (\<forall>x\<in>(event_set es2). \<exists>y\<in>(event_set es1). (justifies_event (label_function es1 y) (label_function es2 x)))"

definition justified_config_reln :: "('a event_structure_data \<times> 'a event_structure_data) set" where
"justified_config_reln \<equiv> { (e1, e2) . justifies_config e1 e2 }"

(*written own reflexive transitive closure for reasons*)
inductive transitive_closure :: "('a  \<Rightarrow> 'a  \<Rightarrow> bool) \<Rightarrow> 'a  \<Rightarrow> 'a  \<Rightarrow> bool" for r where
refl: "transitive_closure r x x "|
step: "r x y \<Longrightarrow> transitive_closure r y z \<Longrightarrow> transitive_closure r x z " 

(*event structure 1 AE justifies event structure 2*)
definition ae_justification :: "'a event_structure_data \<Rightarrow> 'a event_structure_data \<Rightarrow> bool" where
"ae_justification es1 es2 \<equiv> 
  \<forall>x.((trans_closure justifies_config) es1 x) (\<exists>y.((trans_closure justifies_config) x y) \<and> (justifies_config y es2))"

definition empty_ES :: "int event_structure_data" where
"empty_ES \<equiv> 
  \<lparr> event_set = {0},(*contains one Initialisation event*)
  partial_order = \<lambda>x y. False,
  primitive_conflict = \<lambda>x y. False,
  label_function = \<lambda>x.(Label I '''' 0) \<rparr>"


end