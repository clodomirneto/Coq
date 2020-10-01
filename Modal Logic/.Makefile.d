ml0_base.vo ml0_base.glob ml0_base.v.beautified ml0_base.required_vo: ml0_base.v 
ml0_base.vio: ml0_base.v 
ml0_base.vos ml0_base.vok ml0_base.required_vos: ml0_base.v 
ml1_soundness.vo ml1_soundness.glob ml1_soundness.v.beautified ml1_soundness.required_vo: ml1_soundness.v ml0_base.vo
ml1_soundness.vio: ml1_soundness.v ml0_base.vio
ml1_soundness.vos ml1_soundness.vok ml1_soundness.required_vos: ml1_soundness.v ml0_base.vos
ml2_completeness.vo ml2_completeness.glob ml2_completeness.v.beautified ml2_completeness.required_vo: ml2_completeness.v ml1_soundness.vo
ml2_completeness.vio: ml2_completeness.v ml1_soundness.vio
ml2_completeness.vos ml2_completeness.vok ml2_completeness.required_vos: ml2_completeness.v ml1_soundness.vos
ml3_hilbert_calculus.vo ml3_hilbert_calculus.glob ml3_hilbert_calculus.v.beautified ml3_hilbert_calculus.required_vo: ml3_hilbert_calculus.v ml2_completeness.vo
ml3_hilbert_calculus.vio: ml3_hilbert_calculus.v ml2_completeness.vio
ml3_hilbert_calculus.vos ml3_hilbert_calculus.vok ml3_hilbert_calculus.required_vos: ml3_hilbert_calculus.v ml2_completeness.vos
ml4_sequent_calculus.vo ml4_sequent_calculus.glob ml4_sequent_calculus.v.beautified ml4_sequent_calculus.required_vo: ml4_sequent_calculus.v ml2_completeness.vo
ml4_sequent_calculus.vio: ml4_sequent_calculus.v ml2_completeness.vio
ml4_sequent_calculus.vos ml4_sequent_calculus.vok ml4_sequent_calculus.required_vos: ml4_sequent_calculus.v ml2_completeness.vos
ml5_cut_elimination.vo ml5_cut_elimination.glob ml5_cut_elimination.v.beautified ml5_cut_elimination.required_vo: ml5_cut_elimination.v ml4_sequent_calculus.vo
ml5_cut_elimination.vio: ml5_cut_elimination.v ml4_sequent_calculus.vio
ml5_cut_elimination.vos ml5_cut_elimination.vok ml5_cut_elimination.required_vos: ml5_cut_elimination.v ml4_sequent_calculus.vos
