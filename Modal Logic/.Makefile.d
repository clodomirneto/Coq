ml1_soundness.vo ml1_soundness.glob ml1_soundness.v.beautified ml1_soundness.required_vo: ml1_soundness.v 
ml1_soundness.vio: ml1_soundness.v 
ml1_soundness.vos ml1_soundness.vok ml1_soundness.required_vos: ml1_soundness.v 
ml2_completeness.vo ml2_completeness.glob ml2_completeness.v.beautified ml2_completeness.required_vo: ml2_completeness.v ml1_soundness.vo
ml2_completeness.vio: ml2_completeness.v ml1_soundness.vio
ml2_completeness.vos ml2_completeness.vok ml2_completeness.required_vos: ml2_completeness.v ml1_soundness.vos
ml3_hilbert_calculus.vo ml3_hilbert_calculus.glob ml3_hilbert_calculus.v.beautified ml3_hilbert_calculus.required_vo: ml3_hilbert_calculus.v 
ml3_hilbert_calculus.vio: ml3_hilbert_calculus.v 
ml3_hilbert_calculus.vos ml3_hilbert_calculus.vok ml3_hilbert_calculus.required_vos: ml3_hilbert_calculus.v 
