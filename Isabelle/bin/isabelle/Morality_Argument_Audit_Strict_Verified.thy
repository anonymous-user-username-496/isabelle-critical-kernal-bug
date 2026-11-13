theory Morality_Argument_Audit_Strict_Verified
  imports Main
begin

(* ========================================================================= *)
(* PART 1: YOUR EXACT ORIGINAL MORALITY ARGUMENT AUDIT CODE                  *)
(* ========================================================================= *)

text \<open>
  A should is "known" when we know what we should do.
  The two cases are whether a should is known or not.
\<close>

datatype knowledge_case =
    Known_Should
  | No_Known_Should

definition should_known :: "knowledge_case \<Rightarrow> bool" where
  "should_known c \<longleftrightarrow> c = Known_Should"

definition investigate_purpose :: "knowledge_case \<Rightarrow> bool" where
  "investigate_purpose c \<longleftrightarrow> c = No_Known_Should"

text \<open>
  A should remains to be found when its status is not known.
\<close>

definition should_to_be_found :: "knowledge_case \<Rightarrow> bool" where
  "should_to_be_found c \<longleftrightarrow> \<not> should_known c"

lemma cases_exhaustive:
  "c = Known_Should \<or> c = No_Known_Should"
  by (cases c) simp_all

lemma no_known_should_means_investigate:
  assumes "\<not> should_known c"
  shows "investigate_purpose c"
  using assms
  unfolding should_known_def investigate_purpose_def
  by (cases c) simp_all

lemma investigate_when_should_unknown:
  assumes "c = No_Known_Should"
  shows "investigate_purpose c"
  using assms
  unfolding investigate_purpose_def
  by simp

lemma should_to_be_found_iff_investigate:
  "should_to_be_found c \<longleftrightarrow> investigate_purpose c"
  unfolding should_to_be_found_def
    should_known_def investigate_purpose_def
  by (cases c) simp_all

theorem should_status_exhaustive:
  "\<forall>c. should_known c \<or> should_to_be_found c"
proof
  fix c
  show "should_known c \<or> should_to_be_found c"
  proof (cases c)
    case Known_Should
    then show ?thesis
      unfolding should_known_def
      by simp
  next
    case No_Known_Should
    then show ?thesis
      unfolding should_known_def should_to_be_found_def
      by simp
  qed
qed


(* ========================================================================= *)
(* PART 2: PIGDEN'S SYNTACTIC CONSERVATIVITY META-THEOREM                    *)
(* ========================================================================= *)

datatype syn_form =
    DescAtom nat
  | NormOught syn_form
  | Imp syn_form syn_form
  | Bot

primrec has_normative :: "syn_form \<Rightarrow> bool" where
  "has_normative (DescAtom _) = False"
| "has_normative (NormOught _) = True"
| "has_normative (Imp A B) = (has_normative A \<or> has_normative B)"
| "has_normative Bot = False"

inductive desc_provable :: "syn_form set \<Rightarrow> syn_form \<Rightarrow> bool" where
  ax_assume: "A \<in> Gamma \<Longrightarrow> desc_provable Gamma A"
| ax_k: "\<not> has_normative A \<Longrightarrow> \<not> has_normative B \<Longrightarrow> 
         desc_provable Gamma (Imp A (Imp B A))"
| ax_s: "\<not> has_normative A \<Longrightarrow> \<not> has_normative B \<Longrightarrow> \<not> has_normative C \<Longrightarrow> 
         desc_provable Gamma (Imp (Imp A (Imp B C)) (Imp (Imp A B) (Imp A C)))"
| mp: "desc_provable Gamma (Imp A B) \<Longrightarrow> desc_provable Gamma A \<Longrightarrow> desc_provable Gamma B"

theorem pigden_conservativity:
  assumes deriv: "desc_provable Gamma psi"
      and pure_desc: "\<forall>phi \<in> Gamma. \<not> has_normative phi"
  shows "\<not> has_normative psi"
  using deriv pure_desc
proof (induction rule: desc_provable.induct)
  case (ax_assume A Gamma)
  then show ?case by blast
next
  case (ax_k A B Gamma)
  then show ?case by simp
next
  case (ax_s A B C Gamma)
  then show ?case by simp
next
  case (mp Gamma A B)
  have imp_non_norm: "\<not> has_normative (Imp A B)"
    using mp.IH(1) mp.prems by blast
  thus ?case by simp
qed

thm_deps pigden_conservativity


(* ========================================================================= *)
(* PART 3: THE BRIDGE VIOLATION / NEGATION DEMONSTRATION                     *)
(* ========================================================================= *)

theorem negation_of_pigden_demonstration:
  fixes desc_ppa norm_right bridge :: "syn_form"
  assumes def_desc: "desc_ppa = DescAtom 0"
      and def_norm: "norm_right = NormOught (DescAtom 1)"
      and def_bridge: "bridge = Imp desc_ppa norm_right"
  shows "desc_provable {desc_ppa, bridge} norm_right \<and> 
         has_normative norm_right \<and> 
         \<not> (\<forall>phi \<in> {desc_ppa, bridge}. \<not> has_normative phi)"
proof -
  have h1: "desc_provable {desc_ppa, bridge} (Imp desc_ppa norm_right)"
    using ax_assume[of bridge "{desc_ppa, bridge}"] def_bridge by simp
  have h2: "desc_provable {desc_ppa, bridge} desc_ppa"
    using ax_assume[of desc_ppa "{desc_ppa, bridge}"] by simp
  have h_deriv: "desc_provable {desc_ppa, bridge} norm_right"
    using mp[OF h1 h2] .
  have h_norm: "has_normative norm_right"
    using def_norm by simp
  have h_violation: "\<not> (\<forall>phi \<in> {desc_ppa, bridge}. \<not> has_normative phi)"
    using def_bridge def_norm def_desc by auto
  thus ?thesis
    using h_deriv h_norm h_violation by blast
qed

thm_deps negation_of_pigden_demonstration


(* ========================================================================= *)
(* PART 4: RIGOROUS PROOF OF FALSE FROM STRUCTURAL COLLISION                 *)
(* ========================================================================= *)

theorem proves_false_from_collision:
  fixes Gamma :: "syn_form set" and psi :: "syn_form"
  assumes deriv: "desc_provable Gamma psi"
      and pure_desc: "\<forall>phi \<in> Gamma. \<not> has_normative phi"
      and normative_conclusion: "has_normative psi"
  shows False
proof -
  have non_normative: "\<not> has_normative psi"
    using pigden_conservativity[OF deriv pure_desc] .
  thus False
    using normative_conclusion by contradiction
qed

end
