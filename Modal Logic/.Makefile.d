ml0_base.vo ml0_base.glob ml0_base.v.beautified ml0_base.required_vo: ml0_base.v 
ml0_base.vio: ml0_base.v 
ml0_base.vos ml0_base.vok ml0_base.required_vos: ml0_base.v 
ml1_soundness.vo ml1_soundness.glob ml1_soundness.v.beautified ml1_soundness.required_vo: ml1_soundness.v ml0_base.vo
ml1_soundness.vio: ml1_soundness.v ml0_base.vio
ml1_soundness.vos ml1_soundness.vok ml1_soundness.required_vos: ml1_soundness.v ml0_base.vos
ml2_sequent_calculus.vo ml2_sequent_calculus.glob ml2_sequent_calculus.v.beautified ml2_sequent_calculus.required_vo: ml2_sequent_calculus.v ml1_soundness.vo
ml2_sequent_calculus.vio: ml2_sequent_calculus.v ml1_soundness.vio
ml2_sequent_calculus.vos ml2_sequent_calculus.vok ml2_sequent_calculus.required_vos: ml2_sequent_calculus.v ml1_soundness.vos
ml3_cut_elimination.vo ml3_cut_elimination.glob ml3_cut_elimination.v.beautified ml3_cut_elimination.required_vo: ml3_cut_elimination.v ml2_sequent_calculus.vo
ml3_cut_elimination.vio: ml3_cut_elimination.v ml2_sequent_calculus.vio
ml3_cut_elimination.vos ml3_cut_elimination.vok ml3_cut_elimination.required_vos: ml3_cut_elimination.v ml2_sequent_calculus.vos
