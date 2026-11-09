theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  We import your audit file and HOL-Induct.PropLog. 
  We reference the official imported soundness theorem directly. 
  We instantiate soundness with your zero-assumption derivation and its semantic 
  failure witness to formally derive ~ soundness.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume soundness_axiom: soundness

  text \<open>
    1. Retrieve the zero-assumption derivation established in your audit file 
       ({} |- Ought).
    2. Retrieve the semantic failure witness establishing ~( {} |= Ought ).
    3. Specialize PropLog's imported soundness theorem (ALL H p. (H |- p) --> (H |= p)) 
       to our specific zero-assumption derivation.
  \<close>
  
  have derived_ought: "{} |- zero_assumption_formula" 
    by (rule audit_zero_assumption_derivation)

  have semantic_fail: "~ ({} |= zero_assumption_formula)" 
    by (rule audit_semantic_failure_witness)

  have sound_instance: "{} |- zero_assumption_formula --> {} |= zero_assumption_formula"
    using soundness_axiom [rule_format, of "{}" zero_assumption_formula] .

  have semantic_pass: "{} |= zero_assumption_formula"
    using sound_instance derived_ought by blast

  show False
    using semantic_pass semantic_fail by contradiction
qed
thm_deps not_soundness
end
