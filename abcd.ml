

(*===========================================================================*)

let print_typed_var fmt tm =
      let s,ty = dest_var tm in
      pp_print_string fmt ("("^s^":"^string_of_type ty^")") in
    install_user_printer("print_typed_var",print_typed_var);;


(*----For deleting type-----------*)

delete_user_printer "print_typed_var";;

(*===========================================================================*)

(*

I have to load the complex matrix libraries so that the relevant operations, i.e., add, sub and mul should work

needs "Multivariate/cmatrix_theory";;

*)

(*===========================================================================*)
(*         Formalization of ABCD Parameters and Transmission Lines           *)
(*===========================================================================*)

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                Cascaded Transmission Lines (Series Networks)              *)
(*---------------------------------------------------------------------------*)

(*==  Defined new types and verifying their properties on October 17 2023  ==*)

let tl_models_IND,tl_models_REC = define_type
                           "tl_models = ShortTL_SerImp |
                                        ShortTL_ShuAdm |
                                        MediumTL_TCir |
                                        MediumTL_PiCir |
					CascadeTL ";;

(* ------------------------------------------------------------------------- *)
(* For the above type definition HOL Light auotmatically proves two theorems *)
(* ------------------------------------------------------------------------- *)

(*---------------------------------------------------------------------------*)
(*         Theorem 1 (Transmission Lines `tl_models` Induction)              *)
(*---------------------------------------------------------------------------*)
(*

|- !P. P ShortTL_SerImp /\
         P ShortTL_ShuAdm /\
         P MediumTL_TCir /\
         P MediumTL_PiCir /\
         P CascadeTL
         ==> (!x. P x)

*)

g`!P. P ShortTL_SerImp /\
         P ShortTL_ShuAdm /\
         P MediumTL_TCir /\
         P MediumTL_PiCir /\
         P CascadeTL
         ==> (!x. P x)`;;

e (SIMP_TAC [tl_models_IND]);;

let TL_MODELS_IND = top_thm ();;

(*---------------------------------------------------------------------------*)
(*         Theorem 2 (Transmission Lines `tl_models` Recursion)              *)
(*---------------------------------------------------------------------------*)

(*

|- !f0 f1 f2 f3 f4.
         ?fn. fn ShortTL_SerImp = f0 /\
              fn ShortTL_ShuAdm = f1 /\
              fn MediumTL_TCir = f2 /\
              fn MediumTL_PiCir = f3 /\
              fn CascadeTL = f4

*)

g `!f0 f1 f2 f3 f4.
         ?fn. fn ShortTL_SerImp = f0 /\
              fn ShortTL_ShuAdm = f1 /\
              fn MediumTL_TCir = f2 /\
              fn MediumTL_PiCir = f3 /\
              fn CascadeTL = f4`;;

e (SIMP_TAC [tl_models_REC]);;

let TL_MODELS_REC = top_thm ();;

(*--------------------------------------------------------------------------*)

new_type_abbrev ("vol_fun",`:(complex -> complex)`);;
new_type_abbrev ("cur_fun",`:(complex -> complex)`);;
new_type_abbrev ("comp_vec",`:(complex^2)`);;
new_type_abbrev ("comp_mat",`:(complex^2^2)`);;

new_type_abbrev ("R",`:real`);;
new_type_abbrev ("L",`:real`);;
new_type_abbrev ("Ca",`:real`);;
new_type_abbrev ("G",`:real`);;
new_type_abbrev 
     ("trans_lines_const",`:R # L # Ca # G`);;
     
new_type_abbrev ("A",`:complex`);;
new_type_abbrev ("B",`:complex`);;
new_type_abbrev ("C",`:complex`);;
new_type_abbrev ("D",`:complex`);;
new_type_abbrev 
     ("abcd_param",`:A # B # C # D`);;

new_type_abbrev ("Vs",`:vol_fun`);;
new_type_abbrev ("Is",`:cur_fun`);;
new_type_abbrev ("send_end_quan",`:Vs # Is`);;

new_type_abbrev ("VR",`:vol_fun`);;
new_type_abbrev ("IR",`:cur_fun`);;
new_type_abbrev ("recei_end_quan",`:VR # IR`);;

new_type_abbrev ("send_recei_quan",`:send_end_quan # recei_end_quan`);;

(*---------------------------------------------------------------------------*)
(*                Forall (∀) Theorems for Type Abbreviations                 *)
(*---------------------------------------------------------------------------*)

let FORALL_TL_CONST_THM = prove
  (`!P. (!tlc:trans_lines_const. P tlc) <=> !R L CA G. P (R,L,CA,G)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_TL_CONST_THM = prove
  (`!P. (?tlc:trans_lines_const. P tlc) <=> ?R L Ca G. P (R,L,Ca,G)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_ABCD_PARAM_THM = prove
  (`!P. (!tlp:abcd_param. P tlp) <=> !A B C D. P (A,B,C,D)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_ABCD_PARAM_THM = prove
  (`!P. (?tlp:abcd_param. P tlp) <=> ?A B C D. P (A,B,C,D)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_SEND_END_QUAN_THM = prove
  (`!P. (!seq:send_end_quan. P seq) <=> !Vs Is. P (Vs,Is)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_SEND_END_QUAN_THM = prove
  (`!P. (?seq:send_end_quan. P seq) <=> ?Vs Is. P (Vs,Is)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

let FORALL_RECEI_END_QUAN_THM = prove
  (`!P. (!req:send_end_quan. P req) <=> !VR IR. P (VR,IR)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

let EXISTS_RECEI_END_QUAN_THM = prove
  (`!P. (?req:send_end_quan. P req) <=> ?VR IR. P (VR,IR)`,
  REWRITE_TAC[EXISTS_PAIR_THM]);;

(*---------------------------------------------------------------------------*)
(*           General Relationship between
                                the sending and receiving quantities         *)
(*---------------------------------------------------------------------------*)

let send_end_vec = new_definition `
    send_end_vec ((Vs,Is):send_end_quan) z = 
        vector [Vs z; Is z]:comp_vec`;;

let recei_end_vec = new_definition `
    recei_end_vec ((VR,IR):recei_end_quan) z = 
        vector [VR z; IR z]:comp_vec`;;

let abcd_mat_gen = new_definition `
    abcd_mat_gen ((A,B,C,D):abcd_param) = 
        ((vector [vector [A;B]; vector [C;D]]):comp_mat)`;;

let relat_send_receiv_quan_gen = new_definition `
    relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_gen ((A,B,C,D):abcd_param)):comp_mat) ** (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

(*---------------------------------------------------------------------------*)
(*                Definition (Valid Transmission Line Constants)             *)
(*---------------------------------------------------------------------------*)   
       
let valid_tl_const = new_definition `
    valid_tl_const 
        ((R,L,Ca,G):trans_lines_const) = 
                  ((&0 < R) /\ (&0 < L) /\ (&0 < Ca) /\ (&0 < G))`;;

(*---------------------------------------------------------------------------*)
(*                Definition (Valid Transmission Line Model)                 *)
(*---------------------------------------------------------------------------*)   

let valid_transm_line_model = define
  `(valid_transm_line_model (ShortTL_SerImp) <=> T) /\
   (valid_transm_line_model (ShortTL_ShuAdm) <=> T) /\
   (valid_transm_line_model (MediumTL_TCir) <=> T) /\
   (valid_transm_line_model (LongTL_PiCir) <=> T) /\
   (valid_transm_line_model (CascadedTL) <=> T)`;;

(*---------------------------------------------------------------------------*)
(*               Definition (Valid Transmission Line)                        *)
(*---------------------------------------------------------------------------*) 
   
let valid_transmission_line = new_definition
  `valid_transmission_line (tlc,tlm) <=>
    valid_tl_const tlc /\ valid_transm_line_model tlm`;;

(*---------------------------------------------------------------------------*)
(*              Formalization of kcl and kvl in frequency domain             *)
(*---------------------------------------------------------------------------*)

let kcl = new_definition `
    kcl (cur_list:cur_fun list) (z:complex) =
	  ((vsum (0..(LENGTH (cur_list) - 1)) (\n. EL n cur_list z)) = Cx (&0))`;;

let kvl = new_definition `
    kvl (vol_list:vol_fun list) (z:complex) =
	  ((vsum (0..(LENGTH (vol_list) - 1)) (\n. EL n vol_list z)) = Cx (&0))`;;

(*---------------------------------------------------------------------------*)
(*           Component models in Phasor domain (frequency domain)            *)
(*---------------------------------------------------------------------------*)

let resis_volt = new_definition 
    	     `resis_volt (R:real) (Ir:cur_fun) = (\z. Ir z * Cx R)`;;

let conductr = new_definition 
    	     `conductr (R:real) = Cx (&1 / R)`;;

let resis_curr = new_definition 
    	     `resis_curr (R:real) (V:vol_fun) = (\z. V z * conductr R)`;;

let induct_volt = new_definition
      `induct_volt (L:real) (w:real) (Il:cur_fun) =
                                  (\z. ii * Cx w * Cx L * (Il z))`;;

let series_imped_volt = new_definition
      `series_imped_volt (R:real) (L:real) (w:real) (Isi:cur_fun) =
                   (\z. (resis_volt R Isi) z + (induct_volt L w Isi) z)`;;

let induct_curr = new_definition
      `induct_curr (V:vol_fun) (L:real) (w:real) = 
                       (\z. (Cx (&1) / (ii * Cx w * Cx L)) * (V z))`;;

let capacit_volt = new_definition
      `capacit_volt (Ic:vol_fun) (C:real) (w:real) = 
                       (\z. (Cx (&1) / (ii * Cx w * Cx C)) * (Ic z))`;;

let capacit_curr = new_definition
      `capacit_curr (V:vol_fun) (C:real) (w:real) = 
                                  (\z. ii * Cx w * Cx C * (V z))`;;
				  
let shunt_admit_curr = new_definition
      `shunt_admit_curr (R:real) (Ca:real) (w:real) (Vsa:vol_fun) =
                   (\z. (resis_curr R Vsa) z + (capacit_curr Vsa Ca w) z)`;;

(*---------------------------------------------------------------------------*)
(*                         Helping Theorems/Lemmas                           *)
(*---------------------------------------------------------------------------*)

let THREE = 
	prove (`3  = SUC 2`, ARITH_TAC);;

let FOUR = 
	prove (`4  = SUC 3`, ARITH_TAC);;
	
let FIVE = 
	prove (`5  = SUC 4`, ARITH_TAC);;

g `!f1 f2 z.
        vsum (0..1) (\n. EL n [(f1:complex->complex); f2] z) = f1 z + f2 z`;;

e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [ONE]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL; HD]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;

let VSUM_2_LIST = top_thm ();;

g `!f1 f2 f3 z.
        vsum (0..2) (\n. EL n [(f1:complex->complex); f2; f3] z) = f1 z + f2 z + f3 z`;;

e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [TWO]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL]);;
e (SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [ONE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let VSUM_3_LIST = top_thm ();;

g `!f1 f2 f3 f4 z.
        vsum (0..3) (\n. EL n [(f1:complex->complex); f2; f3; f4] z) = f1 z + f2 z + f3 z + f4 z`;;

e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [THREE]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL]);;
e (SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [TWO]);;
e (SIMP_TAC [EL;TL;HD]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (ONCE_REWRITE_TAC [ONE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let VSUM_4_LIST = top_thm ();;

g `!f1 f2 f3 f4 f5 z.
        vsum (0..4) (\n. EL n [(f1:complex->complex); f2; f3; f4; f5] z) = f1 z + f2 z + f3 z + f4 z + f5 z`;;

e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [FOUR]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL]);;
e (SUBGOAL_THEN ` 0 <= SUC 3` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [THREE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [TWO]);;
e (SIMP_TAC [EL;TL;HD]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (ONCE_REWRITE_TAC [ONE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let VSUM_5_LIST = top_thm ();;

g `!f1 f2 f3 f4 f5 f6 z.
        vsum (0..5) (\n. EL n [(f1:complex->complex); f2; f3; f4; f5; f6] z) =
	                                       f1 z + f2 z + f3 z + f4 z + f5 z + f6 z`;;

e (REPEAT GEN_TAC);;
e (ONCE_REWRITE_TAC [FIVE]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL]);;
e (SUBGOAL_THEN ` 0 <= SUC 4` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [FOUR]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SIMP_TAC [EL; TL]);;
e (SUBGOAL_THEN ` 0 <= SUC 3` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [THREE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 2` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ONCE_REWRITE_TAC [TWO]);;
e (SIMP_TAC [EL;TL;HD]);;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 1` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (ONCE_REWRITE_TAC [ONE]);;
e (SIMP_TAC [EL;TL;HD]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [VSUM_CLAUSES_NUMSEG]);;
e (SUBGOAL_THEN ` 0 <= SUC 0` ASSUME_TAC);;
      e (ARITH_TAC) ;;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [EL;TL;HD]);;
e (CONV_TAC COMPLEX_FIELD);;

let VSUM_6_LIST = top_thm ();;

let VEC_MAT_SIMP_TAC xs =
  SIMP_TAC (xs @ [CART_EQ;VECTOR_1;VECTOR_2;VECTOR_3;VECTOR_4; 
                       DIMINDEX_1;DIMINDEX_2;DIMINDEX_3;DIMINDEX_4;
                         FORALL_1; FORALL_2;FORALL_3;FORALL_4;
			  DOT_1; DOT_2;DOT_3;DOT_4;
                           SUM_1;SUM_2;SUM_3;SUM_4]);;

g `!x y (a:complex) b c d.
    ((vector [vector [a; b]; vector [c; d]]):complex^2^2) ** vector [x; y] =
    vector [a * x + b * y ; c * x + d * y]`;;

e (REPEAT GEN_TAC);;
e (CVEC_CMAT_SIMP_TAC [CMATRIX_CVECTOR_MUL_COMPONENT]);;

let MAT2x2_MUL_VEC2 = top_thm ();;

let CMAT_TAC xs =
  SIMP_TAC (xs @ [CART_EQ;VECTOR_2;DIMINDEX_2;FORALL_2;CMULT_2;SUM_2]);;

let CVECTOR2_EQ = prove
  (`!x y z t. vector [x ;y] :complex^2 = vector [z;t] <=> x=z /\ y=t`,
  CMAT_TAC[]);;

(*---------------------------------------------------------------------------*)
(*                 All Transmission Lines KVL Implementations                *)
(*---------------------------------------------------------------------------*)

let admit_curr_med = new_definition
      `admit_curr_med (V:vol_fun) (C:real) (w:real) = 
                                  (\z. Cx w * (Cx C / Cx (&2)) * (V z))`;;

let imped_volt_med = new_definition
      `imped_volt_med (Iz:vol_fun) (R:real) (L:real) (w:real) = 
                                  (\z. ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * (Iz z))`;;

let kvl_implem_1a = define `
   (kvl_implem_1a ShortTL_SerImp
	    ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) (w:real) (z:complex) =
	    (kvl [(\z. Vs z);
		  (\z. --(VR z));
		  resis_volt R (\z. --(IR z));
		  induct_volt L w (\z. --(IR z))] z)) /\
    (kvl_implem_1a ShortTL_ShuAdm (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
         (kvl [(\z. Vs z); (\z. --(VR z))] z))   /\
    (kvl_implem_1a MediumTL_PiCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	    (kvl [(\z. Vs z);
		 (\z. --(VR z));
		 resis_volt R (\z. --(IR z));
		 induct_volt L w (\z. --(IR z));
	         resis_volt R (admit_curr_med (\z. --(VR z)) Ca w);
	         induct_volt L w (admit_curr_med (\z. --(VR z)) Ca w)] z))   /\
    (kvl_implem_1a MediumTL_TCir (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	    (kvl [(\z. Vs z);
		 imped_volt_med (\z. --(Is z)) R L w;
		 (\z. --(VR z));
	         imped_volt_med (\z. --(IR z)) R L w] z))`;;

(*====
(*---------------------------------------------------------------------------*)
(*                          Short Transmission Lines                         *)
(*---------------------------------------------------------------------------*)

let short_circ_series_imped_implem_kvl = new_definition
  `short_circ_series_imped_implem_kvl ShortTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
           (w:real) z ((R,L,Ca,G):trans_lines_const) =
         (kvl [(\z. Vs z); (\z. --(VR z)); resis_volt R (\z. --(IR z)); induct_volt L w (\z. --(IR z))] z)`;;

	      ====*)

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR Ca G L R w z.
   kvl_implem_1a ShortTL_SerImp ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const) (w:real) (z:complex) =
	(Vs z = ((series_imped_volt R L w (IR:cur_fun)) z) + VR z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [series_imped_volt]);;
e (REWRITE_TAC [kvl_implem_1a; kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_4_LIST]);;

e (SUBGOAL_THEN `induct_volt L w (\z. --(IR:cur_fun) z) z = -- (induct_volt L w (\z. IR z) z)` ASSUME_TAC);;
      e (REWRITE_TAC [induct_volt]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC []);;
e (POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `resis_volt R (\z. --(IR:cur_fun) z) z = -- (resis_volt R (\z. IR z) z)` ASSUME_TAC);;
      e (REWRITE_TAC [resis_volt]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC []);;
e (POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SERIES_IMPED_KVL_ALT = top_thm ();;

(*=============================================================*)
(*            Let, in, and form of the above theorem           *)
(*=============================================================*)

g `!Vs Is VR IR Ca G L R w z.
   let se = ((Vs,Is):send_end_quan) and
       re = ((VR,IR):recei_end_quan) and
       tlc = ((R,L,Ca,G):trans_lines_const) in
   (kvl_implem_1a ShortTL_SerImp se re tlc (w:real) (z:complex) =
	(Vs z = ((series_imped_volt R L w (IR:cur_fun)) z) + VR z))`;;

e (LET_TAC);;
e (REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_ALT]);;

let SHORT_TL_SERIES_IMPED_KVL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*                    KCL Implementation Equivalence all                     *)
(*---------------------------------------------------------------------------*)


let kcl_implem_1a = define `
    (kcl_implem_1a ShortTL_SerImp
         ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
          ((R,L,Ca,G):trans_lines_const) (w:real) z =
                   (kcl [(\z. Is z); (\z. --(IR z))] z))   /\
    (kcl_implem_1a ShortTL_ShuAdm
         (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
                   (kcl [(\z. Is z);
		         resis_curr R (\z. --(VR z));
			 capacit_curr (\z. --(VR z)) Ca w;
			 (\z. --(IR z))] z))   /\
    (kcl_implem_1a MediumTL_PiCir
             (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
	           (kcl [(\z. Is z);
		         (\z. --(IR z));
	                 admit_curr_med (\z. --(VR z)) Ca w;
			 admit_curr_med (\z. --(Vs z)) Ca w] z))   /\
    (kcl_implem_1a MediumTL_TCir
             (Vs,Is) (VR,IR) (R,L,Ca,G) w z =
                   (kcl [(\z. Is z);
		         (\z. --(IR z));
	                 (\z. (Cx w * Cx Ca) * ((\z. --(VR z)) z +
			     (imped_volt_med (\z. --(IR z)) R L w) z))] z))`;;

g `!Vs Is VR IR Ca G L R w z.
   kcl_implem_1a ShortTL_SerImp
        ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
         ((R,L,Ca,G):trans_lines_const) (w:real) z = (Is z  = IR z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [kcl_implem_1a; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; SUC_SUB1]);;
e (SIMP_TAC [VSUM_2_LIST]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SERIES_IMPED_KCL_ALT = top_thm ();;

(*=============================================================*)
(*            Let, in, and form of the above theorem           *)
(*=============================================================*)

g `!Vs Is VR IR Ca G L R w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kcl_implem_1a ShortTL_SerImp se re tlc (w:real) z = (Is z = IR z)`;;

e (LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_KCL_ALT]);;

let SHORT_TL_SERIES_IMPED_KCL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*            Verification of the Short Transmisison Lines Models            *)
(*---------------------------------------------------------------------------*)

g `!VR Vs IR Is R L Ca G w z.
   ((kvl_implem_1a ShortTL_SerImp
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) (w:real) z) /\
   (kcl_implem_1a ShortTL_SerImp
       ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) w z)) =
   ((Vs z = (Cx (&1) * VR z + (series_imped_volt R L w (IR:cur_fun)) z)) /\
    (Is z  = Cx (&0) * VR z + Cx (&1) * IR z))`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [SHORT_TL_SERIES_IMPED_KVL_ALT; SHORT_TL_SERIES_IMPED_KCL_ALT]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT = top_thm ();;

(*---------------------------------------------------------------------------*)

g `!VR Vs IR Is R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   ((kvl_implem_1a ShortTL_SerImp se re tlc (w:real) z) /\
   (kcl_implem_1a ShortTL_SerImp se re tlc w z)) =
   ((Vs z = (Cx (&1) * VR z + (series_imped_volt R L w (IR:cur_fun)) z)) /\
    (Is z  = Cx (&0) * VR z + Cx (&1) * IR z))`;;

e (LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT]);;

let SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM = top_thm ();;

(*--------------------------------------------------------------------------*)
(*==  Redefining the final forms of the short and medium models
        (using the tl_models definition) to be
          used in the cascaded TL defintion to model recursive
                                      multiplication of the ABCD matrices ==*)
(*--------------------------------------------------------------------------*)

let abcd_mat_1a = define `
    (abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
	          vector [Cx (&0); Cx (&1)]]):comp_mat))   /\
    (abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); Cx (&0)];
	          vector [(Cx (&1 / R) + ii * Cx w * Cx Ca); Cx (&1)]]):comp_mat)) /\
   (abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  ((Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)))];
	          vector [(Cx w * Cx Ca);
	       (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat)) /\
   (abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  (Cx R + ii * Cx w * Cx L)];
	          vector [((Cx w * Cx Ca) *
                             (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)));
	                  (Cx (&1) +
			     ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`;;
	     

(*------Some useful lemmas proved using definition rewriting------*)


g `!R L Ca G w.
      (abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w =
         ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
  	           vector [Cx (&0); Cx (&1)]]):comp_mat))`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;

let ABCD_MAT_SHORTTL_SER_IMP = top_thm ();;


g `!R L Ca G w.
    (abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); Cx (&0)];
	          vector [(Cx (&1 / R) + ii * Cx w * Cx Ca); Cx (&1)]]):comp_mat))`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;

let ABCD_MAT_SHORTTL_SHU_ADM = top_thm ();;


g `!R L Ca G w.
     (abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  ((Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)))];
	          vector [(Cx w * Cx Ca);
	       (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;

let ABCD_MAT_MEDIUMTL_TCIR = top_thm ();;


g `!R L Ca G w.
      (abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  (Cx R + ii * Cx w * Cx L)];
	          vector [((Cx w * Cx Ca) *
                             (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)));
	                  (Cx (&1) +
			     ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat))`;;

e (REPEAT STRIP_TAC THEN REWRITE_TAC [abcd_mat_1a]);;

let ABCD_MAT_MEDIUMTL_PICIR = top_thm ();;

(*------------------------------------------------------------------------*)

let abcd_mat_short_tl_series_imped = new_definition `
    abcd_mat_short_tl_series_imped ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); (Cx R + ii * Cx w * Cx L)];
	          vector [Cx (&0); Cx (&1)]]):comp_mat)`;;

let relat_send_receiv_quan_short_tl_series_imped = new_definition `
    relat_send_receiv_quan_short_tl_series_imped ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_short_tl_series_imped ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

let relat_send_receiv_quan_1a = define `
    (relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a ShortTL_SerImp ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z)))   /\
    (relat_send_receiv_quan_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a ShortTL_ShuAdm ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))) /\
   (relat_send_receiv_quan_1a MediumTL_PiCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a MediumTL_PiCir ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))) /\
   (relat_send_receiv_quan_1a MediumTL_TCir ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_1a MediumTL_TCir ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z)))`;;

(*-----------------------------------------------------------------------------*)

g `!Vs Is VR IR R L Ca G w z.
    ((kvl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
     (kcl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z))
  = (relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [SHORT_TL_SERIES_IMPED_KVL_KCL_IMP_IMPLEM_ALT; series_imped_volt;
                resis_volt; induct_volt]);;
e (REWRITE_TAC [relat_send_receiv_quan_1a;
                send_end_vec; abcd_mat_1a; recei_end_vec]);;
e (REWRITE_TAC [MAT2x2_MUL_VEC2]);;
e (REWRITE_TAC [CVECTOR2_EQ]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT = top_thm ();;

(*--------------------------------------------------------------------------*)

g `!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    ((kvl_implem_1a ShortTL_SerImp se re tlc w z) /\
     (kcl_implem_1a ShortTL_SerImp se re tlc w z))
  = (relat_send_receiv_quan_1a ShortTL_SerImp se re tlc w z)`;;

e (LET_TAC THEN REWRITE_TAC [SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT]);;

let SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP = top_thm ();;

(*--------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      ((relat_send_receiv_quan_1a ShortTL_SerImp ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)))`;; 

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_1a]);;
e (REWRITE_TAC [abcd_mat_gen; abcd_mat_1a]);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT = top_thm ();;

(*--------------------------------------------------------------------------*)


g `!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      (relat_send_receiv_quan_1a ShortTL_SerImp se re tlc w z))`;; 

e (LET_TAC THEN REWRITE_TAC [ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT]);;

let ABCD_PAR_SHORT_TL_SERIES_IMPED = top_thm ();;

(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      (kvl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z /\
       kcl_implem_1a ShortTL_SerImp (Vs,Is) (VR,IR) (R,L,Ca,G) w z))`;; 

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [SHORT_TL_SERIES_IMPED_IMPLEM_EQ_MAT_REP_ALT]);;
e (ASM_SIMP_TAC [ABCD_PAR_SHORT_TL_SERIES_IMPED_ALT]);;

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP_ALT = top_thm ();;

(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) and
      abcd = ((A,B,C,D):abcd_param) in
     A = Cx(&1) /\
     B = Cx R + ii * Cx w * Cx L /\
     C = Cx(&0) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen se re abcd z) =
      (kvl_implem_1a ShortTL_SerImp se re tlc w z /\
       kcl_implem_1a ShortTL_SerImp se re tlc w z))`;; 

e (LET_TAC THEN REWRITE_TAC [ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP_ALT]);;

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SERIES_IMP = top_thm ();;

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*                 Short Transmission Lines (Shunt Admittance)               *)
(*---------------------------------------------------------------------------*)

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR R L Ca G w z.
   kvl_implem_1a ShortTL_ShuAdm
      ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
        ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = VR z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [kvl_implem_1a;kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_2_LIST]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SHUNT_ADMIT_KVL_ALT = top_thm ();;

(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
   kvl_implem_1a ShortTL_ShuAdm se re tlc w z = (Vs z = VR z)`;;

e (LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KVL_ALT]);;

let SHORT_TL_SHUNT_ADMIT_KVL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR Ca G L R w z.
    kcl_implem_1a ShortTL_ShuAdm ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              ((R,L,Ca,G):trans_lines_const) (w:real) z =
	(Is z = ((shunt_admit_curr R Ca w (VR:vol_fun)) z) + IR z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [shunt_admit_curr]);;
e (REWRITE_TAC [kcl_implem_1a; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_4_LIST]);;

e (SUBGOAL_THEN `resis_curr R (\z. --(VR:cur_fun) z) z = -- (resis_curr R) (\z. VR z) z` ASSUME_TAC);;
      e (REWRITE_TAC [resis_curr]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `capacit_curr (\z. --(VR:cur_fun) z) Ca w z = -- (capacit_curr (\z. VR z) Ca w z)` ASSUME_TAC);;
      e (REWRITE_TAC [capacit_curr]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SHUNT_ADMIT_KCL_ALT = top_thm ();;

(*---------------------------------------------------------------------------*)


g `!Vs Is VR IR R L Ca G w z.
  let se = ((Vs,Is):send_end_quan) and
      re = ((VR,IR):recei_end_quan) and
      tlc = ((R,L,Ca,G):trans_lines_const) in
    kcl_implem_1a ShortTL_ShuAdm se re tlc (w:real) z =
	(Is z = ((shunt_admit_curr R Ca w (VR:vol_fun)) z) + IR z)`;;

e (LET_TAC THEN REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KCL_ALT]);;

let SHORT_TL_SHUNT_ADMIT_KCL = top_thm ();;

(*==Have to start working from here next==*)


(*---------------------------------------------------------------------------*)
(*   Verification of the Short Transmisison Lines Models (Shunt Admittance)  *)
(*---------------------------------------------------------------------------*)

g `!VR Vs IR Is R L Ca G w z.
   ((short_circ_shunt_admit_implem_kvl ShortTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan) z) /\
   (short_circ_shunt_admit_implem_kcl ShortTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              (w:real) z ((R,L,Ca,G):trans_lines_const))) =
	((Vs z  = Cx (&1) * VR z + Cx (&0) * IR z) /\
	 ((Is z = ((shunt_admit_curr (R:real) (Ca:real) (w:real) (VR:vol_fun)) z) + Cx (&1) * IR z)))`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [SHORT_TL_SHUNT_ADMIT_KVL; SHORT_TL_SHUNT_ADMIT_KCL]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM = top_thm ();;

(*--------------------------------------------------------------------------*)

let abcd_mat_short_tl_shunt_admit = new_definition `
    abcd_mat_short_tl_shunt_admit ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [Cx (&1); Cx (&0)];
	          vector [(Cx (&1 / R) + ii * Cx w * Cx Ca); Cx (&1)]]):comp_mat)`;;

let relat_send_receiv_quan_short_tl_shunt_admit = new_definition `
    relat_send_receiv_quan_short_tl_shunt_admit ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_short_tl_shunt_admit ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

g `!Vs Is VR IR R L Ca G w z.
  is_valid_tl ((R,L,Ca,G):trans_lines_const)
  ==> ((short_circ_shunt_admit_implem_kvl ShortTL (Vs,Is) (VR,IR) z) /\
       (short_circ_shunt_admit_implem_kcl ShortTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_short_tl_shunt_admit ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`;;

e (REWRITE_TAC [is_valid_tl]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [SHORT_TL_SHUNT_ADMIT_KVL_KCL_IMP_IMPLEM; shunt_admit_curr;
                resis_curr; capacit_curr]);;
e (REWRITE_TAC [relat_send_receiv_quan_short_tl_shunt_admit;
                send_end_vec; abcd_mat_short_tl_shunt_admit; recei_end_vec]);;
e (REWRITE_TAC [conductr]);;
e (REWRITE_TAC [MAT2x2_MUL_VEC2]);;
e (REWRITE_TAC [CVECTOR2_EQ]);;
e (CONV_TAC COMPLEX_FIELD);;

let SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP = top_thm ();;

(*--------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx (Ca) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      (relat_send_receiv_quan_short_tl_shunt_admit ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z))`;; 

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_short_tl_shunt_admit]);;
e (REWRITE_TAC [abcd_mat_gen; abcd_mat_short_tl_shunt_admit]);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_SHORT_TL_SHUNT_ADMIT = top_thm ();;

g `!Vs Is VR IR A B C D R L Ca G w z.
     is_valid_tl (R,L,Ca,G) /\
     A = Cx(&1) /\
     B = Cx(&0) /\
     C = Cx (&1 / R) + ii * Cx w * Cx (Ca) /\
     D = Cx(&1)
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
      ((short_circ_shunt_admit_implem_kvl ShortTL (Vs,Is) (VR,IR) z) /\
       (short_circ_shunt_admit_implem_kcl ShortTL (Vs,Is) (VR,IR) w z (R,L,Ca,G))))`;; 

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `((short_circ_shunt_admit_implem_kvl ShortTL (Vs,Is) (VR,IR) z) /\
       (short_circ_shunt_admit_implem_kcl ShortTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_short_tl_shunt_admit ShortTL ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)` ASSUME_TAC);;	    
      e (MATCH_MP_TAC SHORT_TL_SHUNT_ADMIT_IMPLEM_EQ_MAT_REP);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ASM_SIMP_TAC [ABCD_PAR_SHORT_TL_SHUNT_ADMIT]);;

let ABCD_PAR_EQ_IMPLEM_SHORT_TL_SHUNT_ADMIT = top_thm ();;


(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*               Medium Transmission Lines (Nominal Pi Circuit)              *)
(*---------------------------------------------------------------------------*)

let admit_curr_med = new_definition
      `admit_curr_med (V:vol_fun) (C:real) (w:real) = 
                                  (\z. Cx w * (Cx C / Cx (&2)) * (V z))`;;

let medium_tl_nomin_pi_circ_implem_kvl = new_definition
  `medium_tl_nomin_pi_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vs z); (\z. --(VR z)); resis_volt R (\z. --(IR z)); induct_volt L w (\z. --(IR z));
	       resis_volt R (admit_curr_med (\z. --(VR z)) Ca w);
	       induct_volt L w (admit_curr_med (\z. --(VR z)) Ca w)] z)`;;

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR R L Ca G w z.
   medium_tl_nomin_pi_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = VR z + (Cx R + ii * Cx w * Cx L) * IR z +
	      (Cx R + ii * Cx w * Cx L) * ((Cx w * Cx Ca) / Cx (&2)) * VR z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [medium_tl_nomin_pi_circ_implem_kvl;kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE; GSYM FOUR; GSYM FIVE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_6_LIST]);;
e (SUBGOAL_THEN `resis_volt R (\z. --(IR:cur_fun) z) z = -- (resis_volt R (\z. IR z) z)` ASSUME_TAC);;
      e (REWRITE_TAC [resis_volt]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SUBGOAL_THEN `(resis_volt R (admit_curr_med (\z. --(VR:vol_fun) z) Ca w) z) = -- (resis_volt R (admit_curr_med (\z. VR z) Ca w) z)` ASSUME_TAC);;
      e (REWRITE_TAC [resis_volt; admit_curr_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [resis_volt; admit_curr_med]);;
e (SUBGOAL_THEN `(induct_volt L w (\z. Cx w * Cx Ca / Cx (&2) * --(VR:vol_fun) z) z) = -- (induct_volt L w (\z. Cx w * Cx Ca / Cx (&2) * VR z) z)` ASSUME_TAC);;
      e (REWRITE_TAC [induct_volt]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [induct_volt]);;
e (SIMP_TAC [ETA_AX]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_KVL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)

let medium_tl_nomin_pi_circ_implem_kcl_s_end = new_definition
  `medium_tl_nomin_pi_circ_implem_kcl_s_end MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Is z); (\z. --(Iz z)); admit_curr_med (\z. --(Vs z)) Ca w] z)`;;

g `!Vs Is VR IR Iz Ca G L R w z.
    medium_tl_nomin_pi_circ_implem_kcl_s_end MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Is z = Iz z + (admit_curr_med Vs Ca w) z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [admit_curr_med]);;
e (REWRITE_TAC [medium_tl_nomin_pi_circ_implem_kcl_s_end; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_3_LIST]);;

e (SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC);;
      e (REWRITE_TAC [admit_curr_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (REWRITE_TAC [admit_curr_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_KCL_SENDING = top_thm ();;

let medium_tl_nomin_pi_circ_implem_kcl_r_end = new_definition
  `medium_tl_nomin_pi_circ_implem_kcl_r_end MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Iz z); (\z. --(IR z));
	       admit_curr_med (\z. --(VR z)) Ca w] z)`;;
	       
g `!Vs Is VR IR Iz Ca G L R w z.
    medium_tl_nomin_pi_circ_implem_kcl_r_end MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
              (Iz:cur_fun) (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Iz z = IR z + (admit_curr_med VR Ca w) z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [admit_curr_med]);;
e (REWRITE_TAC [medium_tl_nomin_pi_circ_implem_kcl_r_end; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_3_LIST]);;

e (SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC);;
      e (REWRITE_TAC [admit_curr_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (REWRITE_TAC [admit_curr_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING = top_thm ();;

let medium_tl_nomin_pi_circ_implem_kcl = new_definition
  `medium_tl_nomin_pi_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
             (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Is z); (\z. --(IR z));
	       admit_curr_med (\z. --(VR z)) Ca w; admit_curr_med (\z. --(Vs z)) Ca w] z)`;;

g `!Vs Is VR IR Ca G L R w z.
    medium_tl_nomin_pi_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
             (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Is z = IR z + (admit_curr_med VR Ca w) z  + (admit_curr_med Vs Ca w) z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [admit_curr_med]);;
e (REWRITE_TAC [medium_tl_nomin_pi_circ_implem_kcl; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_4_LIST]);;

e (SUBGOAL_THEN `!V. admit_curr_med (\z. --V z) Ca w z  = -- (admit_curr_med (\z. V z) Ca w z) ` ASSUME_TAC);;
      e (REWRITE_TAC [admit_curr_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (REWRITE_TAC [admit_curr_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_KCL = top_thm ();;

g `!Vs Is VR IR Iz Ca G L R w z.
    ((medium_tl_nomin_pi_circ_implem_kcl_s_end MediumTL ((Vs,Is):send_end_quan)
          ((VR,IR):recei_end_quan) (Iz:cur_fun) (w:real) z
                 ((R,L,Ca,G):trans_lines_const)) /\
    (medium_tl_nomin_pi_circ_implem_kcl_r_end MediumTL (Vs,Is) (VR,IR) Iz w z
         (R,L,Ca,G))) ==>
      (medium_tl_nomin_pi_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z (R,L,Ca,G))`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [MEDIUM_TL_NOMINAL_PI_KCL; MEDIUM_TL_NOMINAL_PI_KCL_SENDING; MEDIUM_TL_NOMINAL_PI_KCL_RECEIVING]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_SR_IMP_KCL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*    Verification of the Medium Transmission Lines (Nominal Pi Circuit)     *)
(*---------------------------------------------------------------------------*)

g `!VR Vs IR Is R L Ca G w z.
    ((medium_tl_nomin_pi_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
                ((R,L,Ca,G):trans_lines_const) w z) /\
    (medium_tl_nomin_pi_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
                (w:real) z ((R,L,Ca,G):trans_lines_const))) =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) * IR z) /\
     (Is z = ((Cx w * Cx Ca) *
                 (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [MEDIUM_TL_NOMINAL_PI_KVL;MEDIUM_TL_NOMINAL_PI_KCL]);;
e (SIMP_TAC [admit_curr_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM = top_thm ();;

(*--------------------------------------------------------------------------*)

let abcd_mat_medium_tl_nomin_pi_circ = new_definition `
    abcd_mat_medium_tl_nomin_pi_circ ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  (Cx R + ii * Cx w * Cx L)];
	          vector [((Cx w * Cx Ca) *
                             (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)));
	                  (Cx (&1) +
			     ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat)`;;

let relat_send_receiv_quan_medium_tl_nomin_pi_circ = new_definition `
    relat_send_receiv_quan_medium_tl_nomin_pi_circ ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_medium_tl_nomin_pi_circ ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

g `!Vs Is VR IR R L Ca G w z.
  is_valid_tl ((R,L,Ca,G):trans_lines_const)
  ==> ((medium_tl_nomin_pi_circ_implem_kvl MediumTL (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (medium_tl_nomin_pi_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_medium_tl_nomin_pi_circ ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`;;

e (REWRITE_TAC [is_valid_tl]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [MEDIUM_TL_NOMINAL_PI_KVL_KCL_IMP_IMPLEM]);;
e (REWRITE_TAC [relat_send_receiv_quan_medium_tl_nomin_pi_circ;
                send_end_vec; abcd_mat_medium_tl_nomin_pi_circ; recei_end_vec]);;
e (REWRITE_TAC [MAT2x2_MUL_VEC2]);;
e (REWRITE_TAC [CVECTOR2_EQ]);;

let MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP = top_thm ();;

(*--------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          (relat_send_receiv_quan_medium_tl_nomin_pi_circ (Vs,Is) (VR,IR)
             (R,L,Ca,G) w z))`;; 

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_medium_tl_nomin_pi_circ]);;
e (REWRITE_TAC [abcd_mat_gen; abcd_mat_medium_tl_nomin_pi_circ]);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC = top_thm ();;

g `!Vs Is VR IR A B C D R L Ca G w z.
     is_valid_tl (R,L,Ca,G) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          ((medium_tl_nomin_pi_circ_implem_kvl MediumTL (Vs,Is) (VR,IR)
              (R,L,Ca,G) w z) /\
	   (medium_tl_nomin_pi_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z
              (R,L,Ca,G))))`;; 

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `((medium_tl_nomin_pi_circ_implem_kvl MediumTL (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (medium_tl_nomin_pi_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_medium_tl_nomin_pi_circ (Vs,Is) (VR,IR)
         (R,L,Ca,G) w z)` ASSUME_TAC);;	    
      e (MATCH_MP_TAC MEDIUM_TL_NOMINAL_PI_IMPLEM_EQ_MAT_REP);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ASM_SIMP_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_PI_CIRC]);;

let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_PI_CIRC = top_thm ();;

g `!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> ((A * D - B * C) = Cx (&1))`;; 

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC []);;
e (CONV_TAC COMPLEX_FIELD);;

let ABCD_PAR_RELAT_MEDIUM_TL_NOMIN_PI_CIRC = top_thm ();;

g `!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = (Cx R + ii * Cx w * Cx L) /\
     C = ((Cx w * Cx Ca) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) 
      ==> (A = D)`;; 

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_RELAT2_MEDIUM_TL_NOMIN_PI_CIRC = top_thm ();;

(*---------------------------------------------------------------------------*)
(*---------------------------------------------------------------------------*)
(*               Medium Transmission Lines (Nominal T Circuit)               *)
(*---------------------------------------------------------------------------*)
				  
let imped_volt_med = new_definition
      `imped_volt_med (Iz:vol_fun) (R:real) (L:real) (w:real) = 
                                  (\z. ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * (Iz z))`;;

let medium_tl_nomin_t_circ_implem_kvl_loop1 = new_definition
  `medium_tl_nomin_t_circ_implem_kvl_loop1 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vs z); (\z. --(Vy z)); imped_volt_med (\z. --(Is z)) R L w] z)`;;

let medium_tl_nomin_t_circ_implem_kvl_loop2 = new_definition
  `medium_tl_nomin_t_circ_implem_kvl_loop2 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vy z); (\z. --(VR z)); imped_volt_med (\z. --(IR z)) R L w] z)`;;

let medium_tl_nomin_t_circ_implem_kvl = new_definition
  `medium_tl_nomin_t_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
         (kvl [(\z. Vs z); imped_volt_med (\z. --(Is z)) R L w; (\z. --(VR z));
	             imped_volt_med (\z. --(IR z)) R L w] z)`;;

(*---------------------------------------------------------------------------*)
(*                      KVL Implementation Equivalence                       *)
(*---------------------------------------------------------------------------*)

g `!Vs Is VR IR Vy R L Ca G w z.
   medium_tl_nomin_t_circ_implem_kvl_loop1 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = Vy z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [medium_tl_nomin_t_circ_implem_kvl_loop1;kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_3_LIST]);;
e (SUBGOAL_THEN `imped_volt_med (\z. --(Is:cur_fun) z) R L w z = -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC);;
      e (REWRITE_TAC [imped_volt_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [imped_volt_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_KVL_LOOP1 = top_thm ();;

g `!Vs Is VR IR Vy R L Ca G w z.
   medium_tl_nomin_t_circ_implem_kvl_loop2 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z =
	(Vy z = VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [medium_tl_nomin_t_circ_implem_kvl_loop2;kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_3_LIST]);;
e (SUBGOAL_THEN `imped_volt_med (\z. --(Is:cur_fun) z) R L w z = -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC);;
      e (REWRITE_TAC [imped_volt_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [imped_volt_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_KVL_LOOP2 = top_thm ();;

g `!Vs Is VR IR R L Ca G w z.
   medium_tl_nomin_t_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z =
	(Vs z = ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * Is z +
	  VR z + ((Cx R + ii * Cx w * Cx L) / Cx (&2)) * IR z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [medium_tl_nomin_t_circ_implem_kvl;kvl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO; GSYM THREE]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_4_LIST]);;
e (SUBGOAL_THEN `!Is. imped_volt_med (\z. --(Is:cur_fun) z) R L w z = -- (imped_volt_med (\z. Is z) R L w z)` ASSUME_TAC);;
      e (REWRITE_TAC [imped_volt_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (REWRITE_TAC [imped_volt_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_KVL = top_thm ();;

g `!Vs Is VR IR Vy R L Ca G w z.
   (medium_tl_nomin_t_circ_implem_kvl_loop1 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z) /\
   (medium_tl_nomin_t_circ_implem_kvl_loop2 MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            (Vy:vol_fun) ((R,L,Ca,G):trans_lines_const) w z) ==>
   (medium_tl_nomin_t_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z)`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_LOOP1; MEDIUM_TL_NOMINAL_T_KVL_LOOP2; MEDIUM_TL_NOMINAL_T_KVL]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_LOOP12_IMP_KVL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*                     KCL Implementation Equivalence                        *)
(*---------------------------------------------------------------------------*)

let medium_tl_nomin_t_circ_implem_kcl = new_definition
  `medium_tl_nomin_t_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (w:real) z ((R,L,Ca,G):trans_lines_const) =
        (kcl [(\z. Is z); (\z. --(IR z));
	     (\z. (Cx w * Cx Ca) * ((\z. --(VR z)) z + (imped_volt_med (\z. --(IR z)) R L w) z))] z)`;;


g `!Vs Is VR IR Ca G L R w z.
    medium_tl_nomin_t_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (w:real) z ((R,L,Ca,G):trans_lines_const) =
	(Is z = (Cx w * Cx Ca) * VR z + IR z + (Cx w * Cx Ca) * (imped_volt_med IR R L w) z)`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [imped_volt_med]);;
e (REWRITE_TAC [medium_tl_nomin_t_circ_implem_kcl; kcl]);;
e (REWRITE_TAC [LENGTH]);;
e (SIMP_TAC [GSYM ONE; GSYM TWO]);;
e (SIMP_TAC [SUC_SUB1]);;
e (SIMP_TAC [VSUM_3_LIST]);;

e (SUBGOAL_THEN `imped_volt_med (\z. --IR z) R L w z  = -- (imped_volt_med (\z. IR z) R L w z) ` ASSUME_TAC);;
      e (REWRITE_TAC [imped_volt_med]);;
      e (CONV_TAC COMPLEX_FIELD);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (SIMP_TAC [ETA_AX]);;
e (REWRITE_TAC [imped_volt_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_KCL = top_thm ();;

(*---------------------------------------------------------------------------*)
(*     Verification of the Medium Transmission Lines (Nominal T Circuit)     *)
(*---------------------------------------------------------------------------*)

g `!VR Vs IR Is R L Ca G w z.
    ((medium_tl_nomin_t_circ_implem_kvl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
            ((R,L,Ca,G):trans_lines_const) w z) /\
    (medium_tl_nomin_t_circ_implem_kcl MediumTL ((Vs,Is):send_end_quan) ((VR,IR):recei_end_quan)
               (w:real) z ((R,L,Ca,G):trans_lines_const))) =
    ((Vs z  = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * VR z +
               (Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)) * IR z) /\
     (Is z = (Cx w * Cx Ca) * VR z +
              (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) * IR z))`;;

e (REPEAT GEN_TAC);;
e (SIMP_TAC [MEDIUM_TL_NOMINAL_T_KVL; MEDIUM_TL_NOMINAL_T_KCL]);;
e (SIMP_TAC [imped_volt_med]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM = top_thm ();;

(*--------------------------------------------------------------------------*)

let abcd_mat_medium_t_nomin_t_circ1a = new_definition `
    abcd_mat_medium_t_nomin_t_circ1a ((R,L,Ca,G):trans_lines_const) w =
        ((vector [vector [(Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2));
	                  ((Cx R + ii * Cx w * Cx L) *
	        (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4)))];
	          vector [(Cx w * Cx Ca);
	            (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))]]):comp_mat)`;;

let relat_send_receiv_quan_medium_tl_nomin_t_circ1a = new_definition `
    relat_send_receiv_quan_medium_tl_nomin_t_circ1a ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z =
       ((send_end_vec ((Vs,Is):send_end_quan) z) =
          ((abcd_mat_medium_t_nomin_t_circ1a ((R,L,Ca,G):trans_lines_const) w):comp_mat) **
	     (recei_end_vec ((VR,IR):recei_end_quan) z))`;;

g `!Vs Is VR IR R L Ca G w z.
  is_valid_tl ((R,L,Ca,G):trans_lines_const)
  ==> ((medium_tl_nomin_t_circ_implem_kvl MediumTL (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (medium_tl_nomin_t_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_medium_tl_nomin_t_circ1a ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((R,L,Ca,G):trans_lines_const) w z)`;;

e (REWRITE_TAC [is_valid_tl]);;
e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [MEDIUM_TL_NOMINAL_T_KVL_KCL_IMP_IMPLEM]);;
e (REWRITE_TAC [relat_send_receiv_quan_medium_tl_nomin_t_circ1a]);;
e (REWRITE_TAC [send_end_vec; abcd_mat_medium_t_nomin_t_circ1a; recei_end_vec]);;
e (REWRITE_TAC [MAT2x2_MUL_VEC2]);;
e (REWRITE_TAC [CVECTOR2_EQ]);;
e (CONV_TAC COMPLEX_FIELD);;

let MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP = top_thm ();;

(*--------------------------------------------------------------------------*)

g `!Vs Is VR IR A B C D R L Ca G w z.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          (relat_send_receiv_quan_medium_tl_nomin_t_circ1a (Vs,Is) (VR,IR)
             (R,L,Ca,G) w z))`;; 

e (REPEAT STRIP_TAC);;
e (REWRITE_TAC [relat_send_receiv_quan_gen; relat_send_receiv_quan_medium_tl_nomin_t_circ1a]);;
e (REWRITE_TAC [abcd_mat_gen; abcd_mat_medium_t_nomin_t_circ1a]);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC = top_thm ();;

g `!Vs Is VR IR A B C D R L Ca G w z.
     is_valid_tl (R,L,Ca,G) /\
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((relat_send_receiv_quan_gen ((Vs,Is):send_end_quan)
            ((VR,IR):recei_end_quan) ((A,B,C,D):abcd_param) z) =
          ((medium_tl_nomin_t_circ_implem_kvl MediumTL (Vs,Is) (VR,IR)
              (R,L,Ca,G) w z) /\
	   (medium_tl_nomin_t_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z
              (R,L,Ca,G))))`;; 

e (REPEAT STRIP_TAC);;
e (SUBGOAL_THEN `((medium_tl_nomin_t_circ_implem_kvl MediumTL (Vs,Is) (VR,IR) (R,L,Ca,G) w z) /\
       (medium_tl_nomin_t_circ_implem_kcl MediumTL (Vs,Is) (VR,IR) w z (R,L,Ca,G)))
     = (relat_send_receiv_quan_medium_tl_nomin_t_circ1a (Vs,Is) (VR,IR)
         (R,L,Ca,G) w z)` ASSUME_TAC);;	    
      e (MATCH_MP_TAC MEDIUM_TL_NOMINAL_T_IMPLEM_EQ_MAT_REP);;
      e (ASM_SIMP_TAC []);;

e (ASM_SIMP_TAC [] THEN POP_ASSUM (K ALL_TAC));;
e (ASM_SIMP_TAC [ABCD_PAR_MEDIUM_TL_NOMIN_T_CIRC]);;

let ABCD_PAR_EQ_IMPLEM_MEDIUM_TL_NOMIN_T_CIRC = top_thm ();;

g `!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> ((A * D - B * C) = Cx (&1))`;; 

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC []);;
e (CONV_TAC COMPLEX_FIELD);;

let ABCD_PAR_RELAT_MEDIUM_TL_NOMIN_T_CIRC = top_thm ();;

g `!A B C D R L Ca G w.
     A = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2)) /\
     B = ((Cx R + ii * Cx w * Cx L) *
           (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&4))) /\
     C = (Cx w * Cx Ca) /\
     D = (Cx (&1) + ((Cx w * Cx Ca) * (Cx R + ii * Cx w * Cx L)) / Cx (&2))
      ==> (A = D)`;; 

e (REPEAT STRIP_TAC);;
e (ASM_SIMP_TAC []);;

let ABCD_PAR_RELAT2_MEDIUM_TL_NOMIN_T_CIRC = top_thm ();;


(*--------------------------------------------------------------------------*)

new_type_abbrev ("w",`:real`);;

new_type_abbrev 
     ("tl_models_param",`: trans_lines_const # tl_models`);;

new_type_abbrev ("tl_models_param_all",`:tl_models_param list#w`);;

(*======================================================================*)

let cidentity_mat = new_definition
   `cidentity_mat = (vector [vector [Cx (&1); Cx (&0)]; vector [Cx (&0); Cx (&1)]]):complex^2^2`;;

let COMPLEX_CART_EQ = prove
  (`!x y:complex^N. x = y <=> !i. 1 <= i /\ i <= dimindex (:N) ==> x$i = y$i`,
  REWRITE_TAC[CART_EQ]);;

let CCOMMON_TAC xs =
  SIMP_TAC (xs @ [cmatrix_cvector_mul;COMPLEX_CART_EQ;LAMBDA_BETA;
           CART_EQ;VECTOR_2;DIMINDEX_2;FORALL_2;DOT_2;VSUM_2]);;

g `!(A:complex^2^2). A ** cidentity_mat = A`;;

e (GEN_TAC THEN REWRITE_TAC [cidentity_mat]);;
e (CCOMMON_TAC[cmatrix_mul;VECTOR_2;VECTOR_1;LAMBDA_BETA;COMPLEX_MUL_LID;
            COMPLEX_MUL_RID;COMPLEX_MUL_LZERO;COMPLEX_MUL_RZERO;COMPLEX_ADD_LID;
           COMPLEX_ADD_RID]);;

let CMAT_MUL_LID = top_thm ();;

let CMAT_CMAT_MUL = prove
  (`!a b c d p q r (s:complex).
    ((vector [vector [a;b]; vector [c;d]]):complex^2^2) ** ((vector [vector [p;q]; vector [r;s]]):complex^2^2) =
      ((vector [vector [a * p + b * r; a * q + b * s]; vector [c * p + d * r; c * q + d * s]]):complex^2^2)`,

CCOMMON_TAC[cmatrix_mul;VECTOR_2;VECTOR_1;LAMBDA_BETA]);;

let CVECTOR2_EQ = prove
  (`!x y z t:complex. vector [x;y] :complex^2 = vector [z;t] <=> x=z /\ y=t`,
  CCOMMON_TAC[]);;

let CMAT2_EQ = prove
  (`!a b c d p q r (s:complex).
       ((vector [vector [a;b]; vector [c;d]]):complex^2^2) =
       ((vector [vector [p;q]; vector [r;s]]):complex^2^2) <=>
                a = p /\ b = q /\ c = r /\ d = s`,
  CCOMMON_TAC [] THEN CONV_TAC TAUT);;  


(*======================================================================*)
(* The following definition models the cascaded transmission lines.
    It accepts list of parameters of all tranmsision lines that are
     cascaded, i.e., the type "tl_models_param_all" and define the
      cascaded ABCD matrices in term of base case and the induction
       case. For the base case, i.e., no cascaded case, it gives the
        identity matrix, which provides the same output vector
	 corresponding to the input vector. It means that we don't have
	  any transmission line.                                        *)
(*----------------------------------------------------------------------*)
	
let cascaded_abcd_matrix1a = define 
  `cascaded_abcd_matrix1a ([],w) = cidentity_mat /\ 
   cascaded_abcd_matrix1a (CONS ((R,L,Ca,G),tlms) tlmpa,w) =
   (abcd_mat_1a tlms (R,L,Ca,G) w) ** 
     cascaded_abcd_matrix1a (tlmpa,w)`;;

(*======================================================================*)
(*     Verification of the ABCD matrix for the cascaded two-ports
            for example given in the pdf slides (Slide 27/105)
	        a Medium line pi circuit model is cascaded with a
	             short line series impedence model                  *)
(*----------------------------------------------------------------------*)

g `! R1 R2 L1 L2 Ca1 Ca2 G1 G2 w.
   cascaded_abcd_matrix1a ([(R1,L1,Ca1,G1),MediumTL_PiCir;
                            (R2,L2,Ca2,G2),ShortTL_SerImp], w) =
      (vector [vector [Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2);
               ((Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2)) *
	        (Cx R2 + ii * Cx w * Cx L2)) +
		 (Cx R1 + ii * Cx w * Cx L1)];
	       vector [((Cx w * Cx Ca1) *
                       (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4)));
	       (((Cx w * Cx Ca1) *
                 (Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&4))) *
                (Cx R2 + ii * Cx w * Cx L2)) +
		(Cx (&1) + ((Cx w * Cx Ca1) * (Cx R1 + ii * Cx w * Cx L1)) / Cx (&2))]]):complex^2^2`;;

e (REPEAT GEN_TAC);;
e (REWRITE_TAC [cascaded_abcd_matrix1a]);;
e (REWRITE_TAC [abcd_mat_1a]);;
e (REWRITE_TAC [CMAT_MUL_LID]);;
e (REWRITE_TAC [CMAT_CMAT_MUL]);;
e (REWRITE_TAC [CMAT2_EQ]);;
e (CONV_TAC COMPLEX_FIELD);;

let ABCD_MAT_CASCADED_TWO_PORT = top_thm ();;

(*---------------------------------------------------------------------------*)
(*                           Cascaded done                                   *)
(*---------------------------------------------------------------------------*)



(*---------------------------------------------------------------------------*)

