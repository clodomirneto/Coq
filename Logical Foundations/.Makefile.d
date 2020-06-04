c01_basics.vo c01_basics.glob c01_basics.v.beautified c01_basics.required_vo: c01_basics.v 
c01_basics.vio: c01_basics.v 
c01_basics.vos c01_basics.vok c01_basics.required_vos: c01_basics.v 
c02_induction.vo c02_induction.glob c02_induction.v.beautified c02_induction.required_vo: c02_induction.v c01_basics.vo
c02_induction.vio: c02_induction.v c01_basics.vio
c02_induction.vos c02_induction.vok c02_induction.required_vos: c02_induction.v c01_basics.vos
c03_lists.vo c03_lists.glob c03_lists.v.beautified c03_lists.required_vo: c03_lists.v c02_induction.vo
c03_lists.vio: c03_lists.v c02_induction.vio
c03_lists.vos c03_lists.vok c03_lists.required_vos: c03_lists.v c02_induction.vos
c04_poly.vo c04_poly.glob c04_poly.v.beautified c04_poly.required_vo: c04_poly.v c03_lists.vo
c04_poly.vio: c04_poly.v c03_lists.vio
c04_poly.vos c04_poly.vok c04_poly.required_vos: c04_poly.v c03_lists.vos
c05_tactics.vo c05_tactics.glob c05_tactics.v.beautified c05_tactics.required_vo: c05_tactics.v c04_poly.vo
c05_tactics.vio: c05_tactics.v c04_poly.vio
c05_tactics.vos c05_tactics.vok c05_tactics.required_vos: c05_tactics.v c04_poly.vos
c06_logic.vo c06_logic.glob c06_logic.v.beautified c06_logic.required_vo: c06_logic.v c05_tactics.vo
c06_logic.vio: c06_logic.v c05_tactics.vio
c06_logic.vos c06_logic.vok c06_logic.required_vos: c06_logic.v c05_tactics.vos
c07_indprop.vo c07_indprop.glob c07_indprop.v.beautified c07_indprop.required_vo: c07_indprop.v c06_logic.vo
c07_indprop.vio: c07_indprop.v c06_logic.vio
c07_indprop.vos c07_indprop.vok c07_indprop.required_vos: c07_indprop.v c06_logic.vos
