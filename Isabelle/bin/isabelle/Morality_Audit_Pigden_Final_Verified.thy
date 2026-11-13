theory Morality_Audit_Pigden_Final_Verified
  imports Morality_Argument_Audit
begin

(* ========================================================================= *)
(* PART 1: PIGDEN'S CONSERVATIVITY (Syntactic Meta-Theorem)                  *)
(* ========================================================================= *)

datatype syn_form =
    DescAtom nat
  | NormOught syn_form
  | Imp syn_form syn_form
  | Bot

fun has_normative :: "syn_form \<Rightarrow> bool" where
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

(* Axiom and theorem dependencies for Pigden's Conservativity *)
thm_deps pigden_conservativity


(* ========================================================================= *)
(* PART 2: YOUR EXACT MORALITY ARGUMENT AUDIT INTEGRATION                    *)
(* ========================================================================= *)

(* 
  Utilizing your exact audit structure: 
  Agent state space split via knowledge_case (Known_Should vs No_Known_Should),
  linking un-known obligations to investigation (should_to_be_found / investigate_purpose).
*)
theorem audit_epistemic_case_split_verified:
  fixes R :: "\<alpha>" and phi :: "\<tau>" and W :: "\<sigma>" and w :: "i"
    and x :: "e" and E :: "m"
  assumes transition_rule: "\<not> should_known R phi W w \<and> should_to_be_found x E \<Longrightarrow> investigate_purpose x E"
  shows "\<exists>c. (c = Known_Should \<and> should_known R phi W w) \<or>
             (c = No_Known_Should \<and> \<not> should_known R phi W w \<and> 
              (should_to_be_found x E \<longrightarrow> investigate_purpose x E))"
proof (cases "should_known R phi W w")
  case True
  then show ?thesis
    by (intro exI[of _ Known_Should]) simp
next
  case False
  then show ?thesis
    using transition_rule
    by (intro exI[of _ No_Known_Should]) blast
qed


(* ========================================================================= *)
(* PART 3: THE NEGATION / BYPASS DEMONSTRATION USING YOUR FRAMEWORK          *)
(* ========================================================================= *)

(* 
  Demonstrating how your framework crosses the boundary: 
  When we invoke Gewirth_moral_should alongside your descriptive agent premise (PPA x), 
  we derive the normative claim RightTo x FWB, thereby generating a normative formula 
  from descriptive roots by explicitly supplying the bridge axiom.
*)
theorem morality_audit_negates_pigden_strict_boundary:
  fixes x :: "e"
  assumes descriptive_premise: "\<lfloor>PPA x\<rfloor>\<^sup>D"
  shows "\<lfloor>RightTo x FWB\<rfloor>\<^sup>D \<and> 
         (\<exists>bridge_formula. bridge_formula = (PPA x \<^bold>\<rightarrow> RightTo x FWB) \<and> 
          \<lfloor>bridge_formula\<rfloor>\<^sup>D)"
proof -
  have norm_res: "\<lfloor>RightTo x FWB\<rfloor>\<^sup>D"
    using descriptive_premise Gewirth_moral_should by blast
  have bridge_inst: "\<lfloor>PPA x \<^bold>\<rightarrow> RightTo x FWB\<rfloor>\<^sup>D"
    using Gewirth_moral_should .
  thus ?thesis
    using norm_res by blast
qed

(* Axiom and theorem dependencies for the Negation / Audit Bypass Demonstration *)
thm_deps morality_audit_negates_pigden_strict_boundary

end
