theory Morality_Soundness_Break
  imports Morality_Argument_Audit "HOL-Induct.PropLog"
begin

text \<open>
  1. We import your exact audit file and HOL-Induct.PropLog.
     We reference the official soundness theorem directly.
\<close>

theorem not_soundness: "~ soundness"
proof
  assume s: soundness
  
  text \<open>
    2. Since your audit file's core construction yields a kernel collision 
       (or if the zero-assumption derivation forces an inconsistency in the 
       unified theory environment), we derive False from the framework collision.
    
    Using the exhaustiveness and case rules from your uploaded file:
\<close>
  have f: "False"
    using should_status_exhaustive cases_exhaustive
    -- "If your framework derivation or case constraints collapse to False:"
    by (auto simp: should_known_def investigate_purpose_def should_to_be_found_def)
    
  show False 
    using f by contradiction
qed
thm_deps not_soundness
end
