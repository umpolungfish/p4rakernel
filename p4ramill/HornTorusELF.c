// Lean compiler output
// Module: HornTorusELF
// Imports: public import Init
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT uint64_t horn_torus_check(uint64_t);
LEAN_EXPORT uint64_t l_HornTorusELF_z(uint64_t);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_HornTorusELF_countDig16___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HornTorusELF_z___boxed(lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_HornTorusELF_hornTorusCheck___boxed(lean_object*);
LEAN_EXPORT uint64_t l_HornTorusELF_lengthOf(uint64_t);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_HornTorusELF_featureOf64(uint64_t);
LEAN_EXPORT lean_object* l_HornTorusELF_featureOf64___boxed(lean_object*);
uint64_t lean_uint64_sub(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_HornTorusELF_opAt(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_HornTorusELF_countDig16(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_HornTorusELF_opAt___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_HornTorusELF_lengthOf___boxed(lean_object*);
LEAN_EXPORT uint64_t l_HornTorusELF_opAt(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; 
x_3 = 2;
x_4 = lean_uint64_shift_left(x_2, x_3);
x_5 = lean_uint64_shift_right(x_1, x_4);
x_6 = 15;
x_7 = lean_uint64_land(x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_opAt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_HornTorusELF_opAt(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_HornTorusELF_countDig16(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_61; uint64_t x_62; uint64_t x_63; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_93; uint64_t x_94; uint64_t x_95; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_117; uint64_t x_122; uint8_t x_123; 
x_12 = 0;
x_122 = l_HornTorusELF_opAt(x_1, x_12);
x_123 = lean_uint64_dec_eq(x_122, x_2);
if (x_123 == 0)
{
x_117 = x_12;
goto block_121;
}
else
{
uint64_t x_124; 
x_124 = 1;
x_117 = x_124;
goto block_121;
}
block_11:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint8_t x_9; 
x_6 = lean_uint64_add(x_3, x_5);
x_7 = 15;
x_8 = l_HornTorusELF_opAt(x_1, x_7);
x_9 = lean_uint64_dec_eq(x_8, x_2);
if (x_9 == 0)
{
return x_6;
}
else
{
uint64_t x_10; 
x_10 = lean_uint64_add(x_6, x_4);
return x_10;
}
}
block_20:
{
uint64_t x_16; uint64_t x_17; uint64_t x_18; uint8_t x_19; 
x_16 = lean_uint64_add(x_14, x_15);
x_17 = 14;
x_18 = l_HornTorusELF_opAt(x_1, x_17);
x_19 = lean_uint64_dec_eq(x_18, x_2);
if (x_19 == 0)
{
x_3 = x_16;
x_4 = x_13;
x_5 = x_12;
goto block_11;
}
else
{
x_3 = x_16;
x_4 = x_13;
x_5 = x_13;
goto block_11;
}
}
block_28:
{
uint64_t x_24; uint64_t x_25; uint64_t x_26; uint8_t x_27; 
x_24 = lean_uint64_add(x_22, x_23);
x_25 = 13;
x_26 = l_HornTorusELF_opAt(x_1, x_25);
x_27 = lean_uint64_dec_eq(x_26, x_2);
if (x_27 == 0)
{
x_13 = x_21;
x_14 = x_24;
x_15 = x_12;
goto block_20;
}
else
{
x_13 = x_21;
x_14 = x_24;
x_15 = x_21;
goto block_20;
}
}
block_36:
{
uint64_t x_32; uint64_t x_33; uint64_t x_34; uint8_t x_35; 
x_32 = lean_uint64_add(x_30, x_31);
x_33 = 12;
x_34 = l_HornTorusELF_opAt(x_1, x_33);
x_35 = lean_uint64_dec_eq(x_34, x_2);
if (x_35 == 0)
{
x_21 = x_29;
x_22 = x_32;
x_23 = x_12;
goto block_28;
}
else
{
x_21 = x_29;
x_22 = x_32;
x_23 = x_29;
goto block_28;
}
}
block_44:
{
uint64_t x_40; uint64_t x_41; uint64_t x_42; uint8_t x_43; 
x_40 = lean_uint64_add(x_38, x_39);
x_41 = 11;
x_42 = l_HornTorusELF_opAt(x_1, x_41);
x_43 = lean_uint64_dec_eq(x_42, x_2);
if (x_43 == 0)
{
x_29 = x_37;
x_30 = x_40;
x_31 = x_12;
goto block_36;
}
else
{
x_29 = x_37;
x_30 = x_40;
x_31 = x_37;
goto block_36;
}
}
block_52:
{
uint64_t x_48; uint64_t x_49; uint64_t x_50; uint8_t x_51; 
x_48 = lean_uint64_add(x_46, x_47);
x_49 = 10;
x_50 = l_HornTorusELF_opAt(x_1, x_49);
x_51 = lean_uint64_dec_eq(x_50, x_2);
if (x_51 == 0)
{
x_37 = x_45;
x_38 = x_48;
x_39 = x_12;
goto block_44;
}
else
{
x_37 = x_45;
x_38 = x_48;
x_39 = x_45;
goto block_44;
}
}
block_60:
{
uint64_t x_56; uint64_t x_57; uint64_t x_58; uint8_t x_59; 
x_56 = lean_uint64_add(x_53, x_55);
x_57 = 9;
x_58 = l_HornTorusELF_opAt(x_1, x_57);
x_59 = lean_uint64_dec_eq(x_58, x_2);
if (x_59 == 0)
{
x_45 = x_54;
x_46 = x_56;
x_47 = x_12;
goto block_52;
}
else
{
x_45 = x_54;
x_46 = x_56;
x_47 = x_54;
goto block_52;
}
}
block_68:
{
uint64_t x_64; uint64_t x_65; uint64_t x_66; uint8_t x_67; 
x_64 = lean_uint64_add(x_61, x_63);
x_65 = 8;
x_66 = l_HornTorusELF_opAt(x_1, x_65);
x_67 = lean_uint64_dec_eq(x_66, x_2);
if (x_67 == 0)
{
x_53 = x_64;
x_54 = x_62;
x_55 = x_12;
goto block_60;
}
else
{
x_53 = x_64;
x_54 = x_62;
x_55 = x_62;
goto block_60;
}
}
block_76:
{
uint64_t x_72; uint64_t x_73; uint64_t x_74; uint8_t x_75; 
x_72 = lean_uint64_add(x_70, x_71);
x_73 = 7;
x_74 = l_HornTorusELF_opAt(x_1, x_73);
x_75 = lean_uint64_dec_eq(x_74, x_2);
if (x_75 == 0)
{
x_61 = x_72;
x_62 = x_69;
x_63 = x_12;
goto block_68;
}
else
{
x_61 = x_72;
x_62 = x_69;
x_63 = x_69;
goto block_68;
}
}
block_84:
{
uint64_t x_80; uint64_t x_81; uint64_t x_82; uint8_t x_83; 
x_80 = lean_uint64_add(x_78, x_79);
x_81 = 6;
x_82 = l_HornTorusELF_opAt(x_1, x_81);
x_83 = lean_uint64_dec_eq(x_82, x_2);
if (x_83 == 0)
{
x_69 = x_77;
x_70 = x_80;
x_71 = x_12;
goto block_76;
}
else
{
x_69 = x_77;
x_70 = x_80;
x_71 = x_77;
goto block_76;
}
}
block_92:
{
uint64_t x_88; uint64_t x_89; uint64_t x_90; uint8_t x_91; 
x_88 = lean_uint64_add(x_86, x_87);
x_89 = 5;
x_90 = l_HornTorusELF_opAt(x_1, x_89);
x_91 = lean_uint64_dec_eq(x_90, x_2);
if (x_91 == 0)
{
x_77 = x_85;
x_78 = x_88;
x_79 = x_12;
goto block_84;
}
else
{
x_77 = x_85;
x_78 = x_88;
x_79 = x_85;
goto block_84;
}
}
block_100:
{
uint64_t x_96; uint64_t x_97; uint64_t x_98; uint8_t x_99; 
x_96 = lean_uint64_add(x_94, x_95);
x_97 = 4;
x_98 = l_HornTorusELF_opAt(x_1, x_97);
x_99 = lean_uint64_dec_eq(x_98, x_2);
if (x_99 == 0)
{
x_85 = x_93;
x_86 = x_96;
x_87 = x_12;
goto block_92;
}
else
{
x_85 = x_93;
x_86 = x_96;
x_87 = x_93;
goto block_92;
}
}
block_108:
{
uint64_t x_104; uint64_t x_105; uint64_t x_106; uint8_t x_107; 
x_104 = lean_uint64_add(x_102, x_103);
x_105 = 3;
x_106 = l_HornTorusELF_opAt(x_1, x_105);
x_107 = lean_uint64_dec_eq(x_106, x_2);
if (x_107 == 0)
{
x_93 = x_101;
x_94 = x_104;
x_95 = x_12;
goto block_100;
}
else
{
x_93 = x_101;
x_94 = x_104;
x_95 = x_101;
goto block_100;
}
}
block_116:
{
uint64_t x_112; uint64_t x_113; uint64_t x_114; uint8_t x_115; 
x_112 = lean_uint64_add(x_109, x_111);
x_113 = 2;
x_114 = l_HornTorusELF_opAt(x_1, x_113);
x_115 = lean_uint64_dec_eq(x_114, x_2);
if (x_115 == 0)
{
x_101 = x_110;
x_102 = x_112;
x_103 = x_12;
goto block_108;
}
else
{
x_101 = x_110;
x_102 = x_112;
x_103 = x_110;
goto block_108;
}
}
block_121:
{
uint64_t x_118; uint64_t x_119; uint8_t x_120; 
x_118 = 1;
x_119 = l_HornTorusELF_opAt(x_1, x_118);
x_120 = lean_uint64_dec_eq(x_119, x_2);
if (x_120 == 0)
{
x_109 = x_117;
x_110 = x_118;
x_111 = x_12;
goto block_116;
}
else
{
x_109 = x_117;
x_110 = x_118;
x_111 = x_118;
goto block_116;
}
}
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_countDig16___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_HornTorusELF_countDig16(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT uint64_t l_HornTorusELF_lengthOf(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = 16;
x_3 = 0;
x_4 = l_HornTorusELF_countDig16(x_1, x_3);
x_5 = lean_uint64_sub(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_lengthOf___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_HornTorusELF_lengthOf(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_HornTorusELF_featureOf64(uint64_t x_1) {
_start:
{
uint64_t x_2; uint8_t x_3; 
x_2 = 1;
x_3 = lean_uint64_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint64_t x_4; uint8_t x_5; 
x_4 = 2;
x_5 = lean_uint64_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint64_t x_6; uint8_t x_7; 
x_6 = 3;
x_7 = lean_uint64_dec_eq(x_1, x_6);
if (x_7 == 0)
{
uint64_t x_8; uint8_t x_9; 
x_8 = 4;
x_9 = lean_uint64_dec_eq(x_1, x_8);
if (x_9 == 0)
{
uint64_t x_10; uint8_t x_11; 
x_10 = 5;
x_11 = lean_uint64_dec_eq(x_1, x_10);
if (x_11 == 0)
{
uint64_t x_12; uint8_t x_13; 
x_12 = 6;
x_13 = lean_uint64_dec_eq(x_1, x_12);
if (x_13 == 0)
{
return x_8;
}
else
{
uint64_t x_14; 
x_14 = 7;
return x_14;
}
}
else
{
uint64_t x_15; 
x_15 = 6;
return x_15;
}
}
else
{
return x_6;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_featureOf64___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_HornTorusELF_featureOf64(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_HornTorusELF_z(uint64_t x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_sub(x_1, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_z___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_HornTorusELF_z(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t horn_torus_check(uint64_t x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; uint64_t x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; uint8_t x_63; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; uint64_t x_82; uint64_t x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; uint64_t x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; uint64_t x_118; uint64_t x_119; uint64_t x_120; uint64_t x_121; uint64_t x_126; uint64_t x_127; uint64_t x_128; uint64_t x_129; uint64_t x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; uint64_t x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; uint64_t x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; uint64_t x_147; uint64_t x_148; uint64_t x_149; uint64_t x_153; uint64_t x_154; uint64_t x_155; uint64_t x_156; uint64_t x_157; uint64_t x_158; uint64_t x_159; uint64_t x_160; uint64_t x_161; uint64_t x_162; uint64_t x_163; uint64_t x_164; uint64_t x_165; uint64_t x_166; uint64_t x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; uint64_t x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; uint64_t x_182; uint64_t x_183; uint64_t x_184; uint64_t x_185; uint64_t x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; uint64_t x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; uint64_t x_194; uint64_t x_195; uint64_t x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; uint64_t x_201; uint64_t x_202; uint8_t x_203; uint64_t x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; uint64_t x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; uint64_t x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; uint64_t x_218; uint64_t x_219; uint64_t x_220; uint64_t x_221; uint64_t x_222; uint64_t x_223; uint64_t x_224; uint64_t x_225; uint64_t x_226; uint64_t x_227; uint64_t x_228; uint64_t x_229; uint64_t x_230; uint64_t x_231; uint64_t x_232; uint64_t x_239; uint64_t x_240; uint64_t x_241; uint64_t x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; uint64_t x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; uint64_t x_250; uint64_t x_251; uint64_t x_252; uint64_t x_253; uint64_t x_254; uint64_t x_255; uint64_t x_256; uint64_t x_257; uint64_t x_258; uint8_t x_259; uint64_t x_261; uint64_t x_262; uint64_t x_263; uint64_t x_264; uint64_t x_265; uint64_t x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; uint64_t x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; uint64_t x_274; uint64_t x_275; uint64_t x_276; uint64_t x_277; uint64_t x_278; uint64_t x_279; uint64_t x_280; uint64_t x_287; uint64_t x_288; uint64_t x_289; uint64_t x_290; uint64_t x_291; uint64_t x_292; uint64_t x_293; uint64_t x_294; uint64_t x_295; uint64_t x_296; uint64_t x_297; uint64_t x_298; uint64_t x_299; uint64_t x_300; uint64_t x_301; uint64_t x_302; uint64_t x_303; uint64_t x_304; uint64_t x_305; uint8_t x_306; uint64_t x_308; uint64_t x_309; uint64_t x_310; uint64_t x_311; uint64_t x_312; uint64_t x_313; uint64_t x_314; uint64_t x_315; uint64_t x_316; uint64_t x_317; uint64_t x_318; uint64_t x_319; uint64_t x_320; uint64_t x_321; uint64_t x_322; uint64_t x_323; uint64_t x_324; uint64_t x_333; uint64_t x_334; uint64_t x_335; uint64_t x_336; uint64_t x_337; uint64_t x_338; uint64_t x_339; uint64_t x_340; uint64_t x_341; uint64_t x_342; uint64_t x_343; uint64_t x_344; uint64_t x_345; uint64_t x_346; uint64_t x_347; uint64_t x_348; uint8_t x_349; uint64_t x_352; uint64_t x_353; uint64_t x_354; uint64_t x_355; uint64_t x_356; uint64_t x_357; uint64_t x_358; uint64_t x_359; uint64_t x_360; uint64_t x_361; uint64_t x_362; uint64_t x_363; uint64_t x_364; uint64_t x_365; uint64_t x_366; uint64_t x_375; uint64_t x_376; uint64_t x_377; uint64_t x_378; uint64_t x_379; uint64_t x_380; uint64_t x_381; uint64_t x_382; uint64_t x_383; uint64_t x_384; uint64_t x_385; uint64_t x_386; uint64_t x_387; uint64_t x_388; uint8_t x_389; uint64_t x_393; uint64_t x_394; uint64_t x_395; uint64_t x_396; uint64_t x_397; uint64_t x_398; uint64_t x_399; uint64_t x_400; uint64_t x_401; uint64_t x_402; uint64_t x_403; uint64_t x_404; uint64_t x_405; uint64_t x_406; uint64_t x_407; uint64_t x_414; uint64_t x_415; uint64_t x_416; uint64_t x_417; uint64_t x_418; uint64_t x_419; uint64_t x_420; uint64_t x_421; uint64_t x_422; uint64_t x_423; uint64_t x_424; uint64_t x_425; uint64_t x_426; uint64_t x_427; uint8_t x_428; uint64_t x_432; uint64_t x_433; uint64_t x_434; uint64_t x_435; uint64_t x_436; uint64_t x_437; uint64_t x_438; uint64_t x_439; uint64_t x_440; uint64_t x_441; uint64_t x_442; uint64_t x_443; uint64_t x_444; uint64_t x_445; uint64_t x_452; uint64_t x_453; uint64_t x_454; uint64_t x_455; uint64_t x_456; uint64_t x_457; uint64_t x_458; uint64_t x_459; uint64_t x_460; uint64_t x_461; uint64_t x_462; uint64_t x_463; uint64_t x_464; uint8_t x_465; uint64_t x_469; uint64_t x_470; uint64_t x_471; uint64_t x_472; uint64_t x_473; uint64_t x_474; uint64_t x_475; uint64_t x_476; uint64_t x_477; uint64_t x_478; uint64_t x_479; uint64_t x_480; uint64_t x_489; uint64_t x_490; uint64_t x_491; uint64_t x_492; uint64_t x_493; uint64_t x_494; uint64_t x_495; uint64_t x_496; uint64_t x_497; uint64_t x_498; uint64_t x_499; uint64_t x_500; uint64_t x_501; uint64_t x_502; uint64_t x_508; uint64_t x_509; uint64_t x_510; uint64_t x_511; uint64_t x_512; uint64_t x_513; uint64_t x_514; uint64_t x_515; uint64_t x_516; uint64_t x_517; uint64_t x_518; uint64_t x_526; uint64_t x_527; uint64_t x_528; uint64_t x_529; uint64_t x_530; uint64_t x_531; uint64_t x_532; uint64_t x_533; uint64_t x_534; uint64_t x_535; uint64_t x_543; uint64_t x_544; uint64_t x_545; uint64_t x_546; uint64_t x_547; uint64_t x_548; uint64_t x_549; uint64_t x_550; uint64_t x_551; uint64_t x_552; uint64_t x_559; uint64_t x_560; uint64_t x_561; uint64_t x_562; uint64_t x_563; uint64_t x_564; uint64_t x_572; uint64_t x_573; uint64_t x_574; uint64_t x_575; uint64_t x_582; uint64_t x_583; uint64_t x_584; uint64_t x_591; uint64_t x_598; uint64_t x_599; uint8_t x_600; 
x_65 = 44829699028833ULL;
x_66 = lean_uint64_sub(x_1, x_1);
x_205 = lean_uint64_add(x_65, x_66);
x_206 = 2794583943133156129ULL;
x_207 = lean_uint64_add(x_206, x_66);
x_208 = 780003546052385ULL;
x_209 = lean_uint64_add(x_208, x_66);
x_210 = 876062052833638241ULL;
x_211 = lean_uint64_add(x_210, x_66);
x_489 = 48826358077233ULL;
x_490 = lean_uint64_add(x_489, x_66);
x_543 = 16;
x_598 = 4096;
x_599 = lean_uint64_add(x_598, x_66);
x_600 = lean_uint64_dec_eq(x_598, x_599);
if (x_600 == 0)
{
uint64_t x_601; 
x_601 = 0;
x_591 = x_601;
goto block_597;
}
else
{
uint64_t x_602; 
x_602 = 1;
x_591 = x_602;
goto block_597;
}
block_41:
{
uint64_t x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; 
x_22 = lean_uint64_add(x_9, x_7);
x_23 = lean_uint64_add(x_22, x_14);
x_24 = lean_uint64_add(x_23, x_15);
x_25 = lean_uint64_add(x_24, x_4);
x_26 = lean_uint64_add(x_25, x_8);
x_27 = lean_uint64_add(x_26, x_12);
x_28 = lean_uint64_add(x_27, x_6);
x_29 = lean_uint64_add(x_28, x_17);
x_30 = lean_uint64_add(x_29, x_20);
x_31 = lean_uint64_add(x_30, x_5);
x_32 = lean_uint64_add(x_31, x_13);
x_33 = lean_uint64_add(x_32, x_2);
x_34 = lean_uint64_add(x_33, x_19);
x_35 = lean_uint64_add(x_34, x_16);
x_36 = lean_uint64_add(x_35, x_11);
x_37 = lean_uint64_add(x_36, x_3);
x_38 = lean_uint64_add(x_37, x_10);
x_39 = lean_uint64_add(x_38, x_18);
x_40 = lean_uint64_add(x_39, x_21);
return x_40;
}
block_64:
{
if (x_63 == 0)
{
x_2 = x_42;
x_3 = x_43;
x_4 = x_44;
x_5 = x_45;
x_6 = x_46;
x_7 = x_47;
x_8 = x_50;
x_9 = x_51;
x_10 = x_52;
x_11 = x_53;
x_12 = x_54;
x_13 = x_55;
x_14 = x_56;
x_15 = x_57;
x_16 = x_59;
x_17 = x_58;
x_18 = x_60;
x_19 = x_62;
x_20 = x_61;
x_21 = x_49;
goto block_41;
}
else
{
x_2 = x_42;
x_3 = x_43;
x_4 = x_44;
x_5 = x_45;
x_6 = x_46;
x_7 = x_47;
x_8 = x_50;
x_9 = x_51;
x_10 = x_52;
x_11 = x_53;
x_12 = x_54;
x_13 = x_55;
x_14 = x_56;
x_15 = x_57;
x_16 = x_59;
x_17 = x_58;
x_18 = x_60;
x_19 = x_62;
x_20 = x_61;
x_21 = x_48;
goto block_41;
}
}
block_97:
{
uint64_t x_91; uint64_t x_92; uint8_t x_93; 
x_91 = l_HornTorusELF_featureOf64(x_78);
x_92 = lean_uint64_add(x_72, x_66);
x_93 = lean_uint64_dec_eq(x_91, x_92);
if (x_93 == 0)
{
x_42 = x_67;
x_43 = x_68;
x_44 = x_69;
x_45 = x_70;
x_46 = x_71;
x_47 = x_73;
x_48 = x_74;
x_49 = x_75;
x_50 = x_76;
x_51 = x_77;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_84;
x_58 = x_86;
x_59 = x_87;
x_60 = x_90;
x_61 = x_88;
x_62 = x_89;
x_63 = x_93;
goto block_64;
}
else
{
uint64_t x_94; uint64_t x_95; uint8_t x_96; 
x_94 = lean_uint64_add(x_85, x_66);
x_95 = l_HornTorusELF_featureOf64(x_94);
x_96 = lean_uint64_dec_eq(x_95, x_94);
x_42 = x_67;
x_43 = x_68;
x_44 = x_69;
x_45 = x_70;
x_46 = x_71;
x_47 = x_73;
x_48 = x_74;
x_49 = x_75;
x_50 = x_76;
x_51 = x_77;
x_52 = x_79;
x_53 = x_80;
x_54 = x_81;
x_55 = x_82;
x_56 = x_83;
x_57 = x_84;
x_58 = x_86;
x_59 = x_87;
x_60 = x_90;
x_61 = x_88;
x_62 = x_89;
x_63 = x_96;
goto block_64;
}
}
block_125:
{
uint64_t x_122; uint64_t x_123; uint8_t x_124; 
x_122 = l_HornTorusELF_featureOf64(x_112);
x_123 = lean_uint64_add(x_113, x_66);
x_124 = lean_uint64_dec_eq(x_122, x_123);
if (x_124 == 0)
{
x_67 = x_98;
x_68 = x_99;
x_69 = x_100;
x_70 = x_101;
x_71 = x_102;
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_106;
x_76 = x_107;
x_77 = x_108;
x_78 = x_123;
x_79 = x_121;
x_80 = x_109;
x_81 = x_110;
x_82 = x_111;
x_83 = x_114;
x_84 = x_115;
x_85 = x_116;
x_86 = x_118;
x_87 = x_117;
x_88 = x_120;
x_89 = x_119;
x_90 = x_106;
goto block_97;
}
else
{
x_67 = x_98;
x_68 = x_99;
x_69 = x_100;
x_70 = x_101;
x_71 = x_102;
x_72 = x_103;
x_73 = x_104;
x_74 = x_105;
x_75 = x_106;
x_76 = x_107;
x_77 = x_108;
x_78 = x_123;
x_79 = x_121;
x_80 = x_109;
x_81 = x_110;
x_82 = x_111;
x_83 = x_114;
x_84 = x_115;
x_85 = x_116;
x_86 = x_118;
x_87 = x_117;
x_88 = x_120;
x_89 = x_119;
x_90 = x_105;
goto block_97;
}
}
block_152:
{
uint64_t x_150; uint8_t x_151; 
x_150 = l_HornTorusELF_featureOf64(x_146);
x_151 = lean_uint64_dec_eq(x_150, x_146);
if (x_151 == 0)
{
x_98 = x_126;
x_99 = x_149;
x_100 = x_127;
x_101 = x_128;
x_102 = x_129;
x_103 = x_130;
x_104 = x_131;
x_105 = x_132;
x_106 = x_133;
x_107 = x_134;
x_108 = x_135;
x_109 = x_136;
x_110 = x_137;
x_111 = x_138;
x_112 = x_140;
x_113 = x_139;
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_145;
x_118 = x_144;
x_119 = x_148;
x_120 = x_147;
x_121 = x_133;
goto block_125;
}
else
{
x_98 = x_126;
x_99 = x_149;
x_100 = x_127;
x_101 = x_128;
x_102 = x_129;
x_103 = x_130;
x_104 = x_131;
x_105 = x_132;
x_106 = x_133;
x_107 = x_134;
x_108 = x_135;
x_109 = x_136;
x_110 = x_137;
x_111 = x_138;
x_112 = x_140;
x_113 = x_139;
x_114 = x_141;
x_115 = x_142;
x_116 = x_143;
x_117 = x_145;
x_118 = x_144;
x_119 = x_148;
x_120 = x_147;
x_121 = x_132;
goto block_125;
}
}
block_181:
{
uint64_t x_175; uint64_t x_176; uint64_t x_177; uint64_t x_178; uint64_t x_179; uint8_t x_180; 
x_175 = 5;
x_176 = lean_uint64_add(x_175, x_66);
x_177 = l_HornTorusELF_featureOf64(x_176);
x_178 = 6;
x_179 = lean_uint64_add(x_178, x_66);
x_180 = lean_uint64_dec_eq(x_177, x_179);
if (x_180 == 0)
{
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_156;
x_130 = x_157;
x_131 = x_158;
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_174;
x_137 = x_163;
x_138 = x_164;
x_139 = x_165;
x_140 = x_179;
x_141 = x_166;
x_142 = x_167;
x_143 = x_168;
x_144 = x_170;
x_145 = x_169;
x_146 = x_173;
x_147 = x_172;
x_148 = x_171;
x_149 = x_160;
goto block_152;
}
else
{
x_126 = x_153;
x_127 = x_154;
x_128 = x_155;
x_129 = x_156;
x_130 = x_157;
x_131 = x_158;
x_132 = x_159;
x_133 = x_160;
x_134 = x_161;
x_135 = x_162;
x_136 = x_174;
x_137 = x_163;
x_138 = x_164;
x_139 = x_165;
x_140 = x_179;
x_141 = x_166;
x_142 = x_167;
x_143 = x_168;
x_144 = x_170;
x_145 = x_169;
x_146 = x_173;
x_147 = x_172;
x_148 = x_171;
x_149 = x_159;
goto block_152;
}
}
block_204:
{
if (x_203 == 0)
{
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_197;
x_169 = x_199;
x_170 = x_198;
x_171 = x_202;
x_172 = x_201;
x_173 = x_200;
x_174 = x_189;
goto block_181;
}
else
{
x_153 = x_182;
x_154 = x_183;
x_155 = x_184;
x_156 = x_185;
x_157 = x_186;
x_158 = x_187;
x_159 = x_188;
x_160 = x_189;
x_161 = x_190;
x_162 = x_191;
x_163 = x_192;
x_164 = x_193;
x_165 = x_194;
x_166 = x_195;
x_167 = x_196;
x_168 = x_197;
x_169 = x_199;
x_170 = x_198;
x_171 = x_202;
x_172 = x_201;
x_173 = x_200;
x_174 = x_188;
goto block_181;
}
}
block_238:
{
uint64_t x_233; uint8_t x_234; 
x_233 = l_HornTorusELF_countDig16(x_211, x_224);
x_234 = lean_uint64_dec_eq(x_233, x_229);
if (x_234 == 0)
{
x_182 = x_212;
x_183 = x_213;
x_184 = x_214;
x_185 = x_215;
x_186 = x_216;
x_187 = x_217;
x_188 = x_218;
x_189 = x_219;
x_190 = x_220;
x_191 = x_221;
x_192 = x_222;
x_193 = x_223;
x_194 = x_224;
x_195 = x_225;
x_196 = x_226;
x_197 = x_227;
x_198 = x_228;
x_199 = x_232;
x_200 = x_229;
x_201 = x_230;
x_202 = x_231;
x_203 = x_234;
goto block_204;
}
else
{
uint64_t x_235; uint64_t x_236; uint8_t x_237; 
x_235 = 8;
x_236 = l_HornTorusELF_countDig16(x_211, x_235);
x_237 = lean_uint64_dec_eq(x_236, x_229);
x_182 = x_212;
x_183 = x_213;
x_184 = x_214;
x_185 = x_215;
x_186 = x_216;
x_187 = x_217;
x_188 = x_218;
x_189 = x_219;
x_190 = x_220;
x_191 = x_221;
x_192 = x_222;
x_193 = x_223;
x_194 = x_224;
x_195 = x_225;
x_196 = x_226;
x_197 = x_227;
x_198 = x_228;
x_199 = x_232;
x_200 = x_229;
x_201 = x_230;
x_202 = x_231;
x_203 = x_237;
goto block_204;
}
}
block_260:
{
if (x_259 == 0)
{
x_212 = x_239;
x_213 = x_240;
x_214 = x_241;
x_215 = x_242;
x_216 = x_243;
x_217 = x_244;
x_218 = x_245;
x_219 = x_246;
x_220 = x_247;
x_221 = x_248;
x_222 = x_249;
x_223 = x_250;
x_224 = x_251;
x_225 = x_252;
x_226 = x_253;
x_227 = x_254;
x_228 = x_255;
x_229 = x_258;
x_230 = x_257;
x_231 = x_256;
x_232 = x_246;
goto block_238;
}
else
{
x_212 = x_239;
x_213 = x_240;
x_214 = x_241;
x_215 = x_242;
x_216 = x_243;
x_217 = x_244;
x_218 = x_245;
x_219 = x_246;
x_220 = x_247;
x_221 = x_248;
x_222 = x_249;
x_223 = x_250;
x_224 = x_251;
x_225 = x_252;
x_226 = x_253;
x_227 = x_254;
x_228 = x_255;
x_229 = x_258;
x_230 = x_257;
x_231 = x_256;
x_232 = x_245;
goto block_238;
}
}
block_286:
{
uint64_t x_281; uint8_t x_282; 
x_281 = l_HornTorusELF_countDig16(x_209, x_273);
x_282 = lean_uint64_dec_eq(x_281, x_279);
if (x_282 == 0)
{
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = x_264;
x_243 = x_265;
x_244 = x_266;
x_245 = x_267;
x_246 = x_268;
x_247 = x_269;
x_248 = x_270;
x_249 = x_271;
x_250 = x_272;
x_251 = x_273;
x_252 = x_274;
x_253 = x_275;
x_254 = x_276;
x_255 = x_277;
x_256 = x_280;
x_257 = x_278;
x_258 = x_279;
x_259 = x_282;
goto block_260;
}
else
{
uint64_t x_283; uint64_t x_284; uint8_t x_285; 
x_283 = 8;
x_284 = l_HornTorusELF_countDig16(x_209, x_283);
x_285 = lean_uint64_dec_eq(x_284, x_279);
x_239 = x_261;
x_240 = x_262;
x_241 = x_263;
x_242 = x_264;
x_243 = x_265;
x_244 = x_266;
x_245 = x_267;
x_246 = x_268;
x_247 = x_269;
x_248 = x_270;
x_249 = x_271;
x_250 = x_272;
x_251 = x_273;
x_252 = x_274;
x_253 = x_275;
x_254 = x_276;
x_255 = x_277;
x_256 = x_280;
x_257 = x_278;
x_258 = x_279;
x_259 = x_285;
goto block_260;
}
}
block_307:
{
if (x_306 == 0)
{
x_261 = x_287;
x_262 = x_288;
x_263 = x_289;
x_264 = x_290;
x_265 = x_291;
x_266 = x_292;
x_267 = x_293;
x_268 = x_294;
x_269 = x_295;
x_270 = x_296;
x_271 = x_297;
x_272 = x_298;
x_273 = x_299;
x_274 = x_300;
x_275 = x_301;
x_276 = x_302;
x_277 = x_303;
x_278 = x_305;
x_279 = x_304;
x_280 = x_294;
goto block_286;
}
else
{
x_261 = x_287;
x_262 = x_288;
x_263 = x_289;
x_264 = x_290;
x_265 = x_291;
x_266 = x_292;
x_267 = x_293;
x_268 = x_294;
x_269 = x_295;
x_270 = x_296;
x_271 = x_297;
x_272 = x_298;
x_273 = x_299;
x_274 = x_300;
x_275 = x_301;
x_276 = x_302;
x_277 = x_303;
x_278 = x_305;
x_279 = x_304;
x_280 = x_293;
goto block_286;
}
}
block_332:
{
uint64_t x_325; uint64_t x_326; uint64_t x_327; uint8_t x_328; 
x_325 = l_HornTorusELF_countDig16(x_205, x_318);
x_326 = 1;
x_327 = lean_uint64_add(x_326, x_66);
x_328 = lean_uint64_dec_eq(x_325, x_327);
if (x_328 == 0)
{
x_287 = x_324;
x_288 = x_308;
x_289 = x_309;
x_290 = x_310;
x_291 = x_311;
x_292 = x_312;
x_293 = x_326;
x_294 = x_313;
x_295 = x_314;
x_296 = x_315;
x_297 = x_316;
x_298 = x_317;
x_299 = x_318;
x_300 = x_319;
x_301 = x_320;
x_302 = x_321;
x_303 = x_322;
x_304 = x_327;
x_305 = x_323;
x_306 = x_328;
goto block_307;
}
else
{
uint64_t x_329; uint64_t x_330; uint8_t x_331; 
x_329 = 8;
x_330 = l_HornTorusELF_countDig16(x_205, x_329);
x_331 = lean_uint64_dec_eq(x_330, x_327);
x_287 = x_324;
x_288 = x_308;
x_289 = x_309;
x_290 = x_310;
x_291 = x_311;
x_292 = x_312;
x_293 = x_326;
x_294 = x_313;
x_295 = x_314;
x_296 = x_315;
x_297 = x_316;
x_298 = x_317;
x_299 = x_318;
x_300 = x_319;
x_301 = x_320;
x_302 = x_321;
x_303 = x_322;
x_304 = x_327;
x_305 = x_323;
x_306 = x_331;
goto block_307;
}
}
block_351:
{
if (x_349 == 0)
{
x_308 = x_333;
x_309 = x_334;
x_310 = x_335;
x_311 = x_336;
x_312 = x_337;
x_313 = x_338;
x_314 = x_339;
x_315 = x_340;
x_316 = x_341;
x_317 = x_342;
x_318 = x_343;
x_319 = x_344;
x_320 = x_345;
x_321 = x_346;
x_322 = x_347;
x_323 = x_348;
x_324 = x_338;
goto block_332;
}
else
{
uint64_t x_350; 
x_350 = 1;
x_308 = x_333;
x_309 = x_334;
x_310 = x_335;
x_311 = x_336;
x_312 = x_337;
x_313 = x_338;
x_314 = x_339;
x_315 = x_340;
x_316 = x_341;
x_317 = x_342;
x_318 = x_343;
x_319 = x_344;
x_320 = x_345;
x_321 = x_346;
x_322 = x_347;
x_323 = x_348;
x_324 = x_350;
goto block_332;
}
}
block_374:
{
uint64_t x_367; uint64_t x_368; uint64_t x_369; uint8_t x_370; 
x_367 = 0;
x_368 = 9;
x_369 = l_HornTorusELF_countDig16(x_209, x_368);
x_370 = lean_uint64_dec_lt(x_66, x_369);
if (x_370 == 0)
{
x_333 = x_352;
x_334 = x_353;
x_335 = x_354;
x_336 = x_355;
x_337 = x_356;
x_338 = x_367;
x_339 = x_357;
x_340 = x_358;
x_341 = x_359;
x_342 = x_366;
x_343 = x_360;
x_344 = x_361;
x_345 = x_362;
x_346 = x_363;
x_347 = x_364;
x_348 = x_365;
x_349 = x_370;
goto block_351;
}
else
{
uint64_t x_371; uint64_t x_372; uint8_t x_373; 
x_371 = 10;
x_372 = l_HornTorusELF_countDig16(x_209, x_371);
x_373 = lean_uint64_dec_lt(x_66, x_372);
x_333 = x_352;
x_334 = x_353;
x_335 = x_354;
x_336 = x_355;
x_337 = x_356;
x_338 = x_367;
x_339 = x_357;
x_340 = x_358;
x_341 = x_359;
x_342 = x_366;
x_343 = x_360;
x_344 = x_361;
x_345 = x_362;
x_346 = x_363;
x_347 = x_364;
x_348 = x_365;
x_349 = x_373;
goto block_351;
}
}
block_392:
{
if (x_389 == 0)
{
uint64_t x_390; 
x_390 = 0;
x_352 = x_375;
x_353 = x_376;
x_354 = x_377;
x_355 = x_378;
x_356 = x_379;
x_357 = x_380;
x_358 = x_381;
x_359 = x_382;
x_360 = x_383;
x_361 = x_384;
x_362 = x_385;
x_363 = x_386;
x_364 = x_387;
x_365 = x_388;
x_366 = x_390;
goto block_374;
}
else
{
uint64_t x_391; 
x_391 = 1;
x_352 = x_375;
x_353 = x_376;
x_354 = x_377;
x_355 = x_378;
x_356 = x_379;
x_357 = x_380;
x_358 = x_381;
x_359 = x_382;
x_360 = x_383;
x_361 = x_384;
x_362 = x_385;
x_363 = x_386;
x_364 = x_387;
x_365 = x_388;
x_366 = x_391;
goto block_374;
}
}
block_413:
{
uint64_t x_408; uint8_t x_409; 
x_408 = l_HornTorusELF_opAt(x_211, x_404);
x_409 = lean_uint64_dec_eq(x_408, x_401);
if (x_409 == 0)
{
x_375 = x_393;
x_376 = x_407;
x_377 = x_394;
x_378 = x_395;
x_379 = x_396;
x_380 = x_398;
x_381 = x_399;
x_382 = x_400;
x_383 = x_401;
x_384 = x_402;
x_385 = x_403;
x_386 = x_404;
x_387 = x_405;
x_388 = x_406;
x_389 = x_409;
goto block_392;
}
else
{
uint64_t x_410; uint64_t x_411; uint8_t x_412; 
x_410 = l_HornTorusELF_opAt(x_211, x_397);
x_411 = 8;
x_412 = lean_uint64_dec_eq(x_410, x_411);
x_375 = x_393;
x_376 = x_407;
x_377 = x_394;
x_378 = x_395;
x_379 = x_396;
x_380 = x_398;
x_381 = x_399;
x_382 = x_400;
x_383 = x_401;
x_384 = x_402;
x_385 = x_403;
x_386 = x_404;
x_387 = x_405;
x_388 = x_406;
x_389 = x_412;
goto block_392;
}
}
block_431:
{
if (x_428 == 0)
{
uint64_t x_429; 
x_429 = 0;
x_393 = x_414;
x_394 = x_415;
x_395 = x_416;
x_396 = x_417;
x_397 = x_418;
x_398 = x_419;
x_399 = x_420;
x_400 = x_421;
x_401 = x_422;
x_402 = x_423;
x_403 = x_424;
x_404 = x_425;
x_405 = x_426;
x_406 = x_427;
x_407 = x_429;
goto block_413;
}
else
{
uint64_t x_430; 
x_430 = 1;
x_393 = x_414;
x_394 = x_415;
x_395 = x_416;
x_396 = x_417;
x_397 = x_418;
x_398 = x_419;
x_399 = x_420;
x_400 = x_421;
x_401 = x_422;
x_402 = x_423;
x_403 = x_424;
x_404 = x_425;
x_405 = x_426;
x_406 = x_427;
x_407 = x_430;
goto block_413;
}
}
block_451:
{
uint64_t x_446; uint8_t x_447; 
x_446 = l_HornTorusELF_opAt(x_209, x_443);
x_447 = lean_uint64_dec_eq(x_446, x_440);
if (x_447 == 0)
{
x_414 = x_432;
x_415 = x_433;
x_416 = x_434;
x_417 = x_435;
x_418 = x_436;
x_419 = x_437;
x_420 = x_438;
x_421 = x_439;
x_422 = x_440;
x_423 = x_441;
x_424 = x_442;
x_425 = x_443;
x_426 = x_444;
x_427 = x_445;
x_428 = x_447;
goto block_431;
}
else
{
uint64_t x_448; uint64_t x_449; uint8_t x_450; 
x_448 = 8;
x_449 = l_HornTorusELF_opAt(x_209, x_448);
x_450 = lean_uint64_dec_eq(x_449, x_448);
x_414 = x_432;
x_415 = x_433;
x_416 = x_434;
x_417 = x_435;
x_418 = x_436;
x_419 = x_437;
x_420 = x_438;
x_421 = x_439;
x_422 = x_440;
x_423 = x_441;
x_424 = x_442;
x_425 = x_443;
x_426 = x_444;
x_427 = x_445;
x_428 = x_450;
goto block_431;
}
}
block_468:
{
if (x_465 == 0)
{
uint64_t x_466; 
x_466 = 0;
x_432 = x_452;
x_433 = x_453;
x_434 = x_454;
x_435 = x_455;
x_436 = x_456;
x_437 = x_457;
x_438 = x_458;
x_439 = x_459;
x_440 = x_460;
x_441 = x_461;
x_442 = x_462;
x_443 = x_463;
x_444 = x_464;
x_445 = x_466;
goto block_451;
}
else
{
uint64_t x_467; 
x_467 = 1;
x_432 = x_452;
x_433 = x_453;
x_434 = x_454;
x_435 = x_455;
x_436 = x_456;
x_437 = x_457;
x_438 = x_458;
x_439 = x_459;
x_440 = x_460;
x_441 = x_461;
x_442 = x_462;
x_443 = x_463;
x_444 = x_464;
x_445 = x_467;
goto block_451;
}
}
block_488:
{
uint64_t x_481; uint64_t x_482; uint8_t x_483; 
x_481 = l_HornTorusELF_opAt(x_205, x_479);
x_482 = 7;
x_483 = lean_uint64_dec_eq(x_481, x_482);
if (x_483 == 0)
{
x_452 = x_470;
x_453 = x_471;
x_454 = x_474;
x_455 = x_473;
x_456 = x_477;
x_457 = x_476;
x_458 = x_478;
x_459 = x_469;
x_460 = x_482;
x_461 = x_472;
x_462 = x_475;
x_463 = x_479;
x_464 = x_480;
x_465 = x_483;
goto block_468;
}
else
{
uint64_t x_484; uint64_t x_485; uint64_t x_486; uint8_t x_487; 
x_484 = 10;
x_485 = l_HornTorusELF_opAt(x_205, x_484);
x_486 = 8;
x_487 = lean_uint64_dec_eq(x_485, x_486);
x_452 = x_470;
x_453 = x_471;
x_454 = x_474;
x_455 = x_473;
x_456 = x_477;
x_457 = x_476;
x_458 = x_478;
x_459 = x_469;
x_460 = x_482;
x_461 = x_472;
x_462 = x_475;
x_463 = x_479;
x_464 = x_480;
x_465 = x_487;
goto block_468;
}
}
block_507:
{
uint64_t x_503; uint8_t x_504; 
x_503 = l_HornTorusELF_lengthOf(x_490);
x_504 = lean_uint64_dec_eq(x_503, x_497);
if (x_504 == 0)
{
uint64_t x_505; 
x_505 = 0;
x_469 = x_491;
x_470 = x_492;
x_471 = x_502;
x_472 = x_493;
x_473 = x_495;
x_474 = x_494;
x_475 = x_496;
x_476 = x_499;
x_477 = x_498;
x_478 = x_501;
x_479 = x_500;
x_480 = x_505;
goto block_488;
}
else
{
uint64_t x_506; 
x_506 = 1;
x_469 = x_491;
x_470 = x_492;
x_471 = x_502;
x_472 = x_493;
x_473 = x_495;
x_474 = x_494;
x_475 = x_496;
x_476 = x_499;
x_477 = x_498;
x_478 = x_501;
x_479 = x_500;
x_480 = x_506;
goto block_488;
}
}
block_525:
{
uint64_t x_519; uint64_t x_520; uint64_t x_521; uint8_t x_522; 
x_519 = l_HornTorusELF_lengthOf(x_211);
x_520 = 15;
x_521 = lean_uint64_add(x_520, x_66);
x_522 = lean_uint64_dec_eq(x_519, x_521);
if (x_522 == 0)
{
uint64_t x_523; 
x_523 = 0;
x_491 = x_518;
x_492 = x_508;
x_493 = x_509;
x_494 = x_511;
x_495 = x_510;
x_496 = x_512;
x_497 = x_515;
x_498 = x_514;
x_499 = x_513;
x_500 = x_517;
x_501 = x_516;
x_502 = x_523;
goto block_507;
}
else
{
uint64_t x_524; 
x_524 = 1;
x_491 = x_518;
x_492 = x_508;
x_493 = x_509;
x_494 = x_511;
x_495 = x_510;
x_496 = x_512;
x_497 = x_515;
x_498 = x_514;
x_499 = x_513;
x_500 = x_517;
x_501 = x_516;
x_502 = x_524;
goto block_507;
}
}
block_542:
{
uint64_t x_536; uint64_t x_537; uint64_t x_538; uint8_t x_539; 
x_536 = l_HornTorusELF_lengthOf(x_209);
x_537 = 13;
x_538 = lean_uint64_add(x_537, x_66);
x_539 = lean_uint64_dec_eq(x_536, x_538);
if (x_539 == 0)
{
uint64_t x_540; 
x_540 = 0;
x_508 = x_526;
x_509 = x_527;
x_510 = x_529;
x_511 = x_528;
x_512 = x_530;
x_513 = x_535;
x_514 = x_532;
x_515 = x_531;
x_516 = x_534;
x_517 = x_533;
x_518 = x_540;
goto block_525;
}
else
{
uint64_t x_541; 
x_541 = 1;
x_508 = x_526;
x_509 = x_527;
x_510 = x_529;
x_511 = x_528;
x_512 = x_530;
x_513 = x_535;
x_514 = x_532;
x_515 = x_531;
x_516 = x_534;
x_517 = x_533;
x_518 = x_541;
goto block_525;
}
}
block_558:
{
uint64_t x_553; uint64_t x_554; uint8_t x_555; 
x_553 = l_HornTorusELF_lengthOf(x_207);
x_554 = lean_uint64_add(x_543, x_66);
x_555 = lean_uint64_dec_eq(x_553, x_554);
if (x_555 == 0)
{
uint64_t x_556; 
x_556 = 0;
x_526 = x_552;
x_527 = x_544;
x_528 = x_546;
x_529 = x_545;
x_530 = x_547;
x_531 = x_549;
x_532 = x_548;
x_533 = x_551;
x_534 = x_550;
x_535 = x_556;
goto block_542;
}
else
{
uint64_t x_557; 
x_557 = 1;
x_526 = x_552;
x_527 = x_544;
x_528 = x_546;
x_529 = x_545;
x_530 = x_547;
x_531 = x_549;
x_532 = x_548;
x_533 = x_551;
x_534 = x_550;
x_535 = x_557;
goto block_542;
}
}
block_571:
{
uint64_t x_565; uint64_t x_566; uint64_t x_567; uint8_t x_568; 
x_565 = l_HornTorusELF_lengthOf(x_205);
x_566 = 12;
x_567 = lean_uint64_add(x_566, x_66);
x_568 = lean_uint64_dec_eq(x_565, x_567);
if (x_568 == 0)
{
uint64_t x_569; 
x_569 = 0;
x_544 = x_559;
x_545 = x_561;
x_546 = x_560;
x_547 = x_564;
x_548 = x_566;
x_549 = x_567;
x_550 = x_563;
x_551 = x_562;
x_552 = x_569;
goto block_558;
}
else
{
uint64_t x_570; 
x_570 = 1;
x_544 = x_559;
x_545 = x_561;
x_546 = x_560;
x_547 = x_564;
x_548 = x_566;
x_549 = x_567;
x_550 = x_563;
x_551 = x_562;
x_552 = x_570;
goto block_558;
}
}
block_581:
{
uint64_t x_576; uint64_t x_577; uint8_t x_578; 
x_576 = 4;
x_577 = lean_uint64_add(x_543, x_66);
x_578 = lean_uint64_dec_eq(x_543, x_577);
if (x_578 == 0)
{
uint64_t x_579; 
x_579 = 0;
x_559 = x_575;
x_560 = x_576;
x_561 = x_572;
x_562 = x_574;
x_563 = x_573;
x_564 = x_579;
goto block_571;
}
else
{
uint64_t x_580; 
x_580 = 1;
x_559 = x_575;
x_560 = x_576;
x_561 = x_572;
x_562 = x_574;
x_563 = x_573;
x_564 = x_580;
goto block_571;
}
}
block_590:
{
uint64_t x_585; uint64_t x_586; uint8_t x_587; 
x_585 = 2048;
x_586 = lean_uint64_add(x_585, x_66);
x_587 = lean_uint64_dec_eq(x_585, x_586);
if (x_587 == 0)
{
uint64_t x_588; 
x_588 = 0;
x_572 = x_584;
x_573 = x_583;
x_574 = x_582;
x_575 = x_588;
goto block_581;
}
else
{
uint64_t x_589; 
x_589 = 1;
x_572 = x_584;
x_573 = x_583;
x_574 = x_582;
x_575 = x_589;
goto block_581;
}
}
block_597:
{
uint64_t x_592; uint64_t x_593; uint8_t x_594; 
x_592 = 2;
x_593 = lean_uint64_add(x_543, x_66);
x_594 = lean_uint64_dec_eq(x_543, x_593);
if (x_594 == 0)
{
uint64_t x_595; 
x_595 = 0;
x_582 = x_592;
x_583 = x_591;
x_584 = x_595;
goto block_590;
}
else
{
uint64_t x_596; 
x_596 = 1;
x_582 = x_592;
x_583 = x_591;
x_584 = x_596;
goto block_590;
}
}
}
}
LEAN_EXPORT lean_object* l_HornTorusELF_hornTorusCheck___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = horn_torus_check(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
lean_object* initialize_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_HornTorusELF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
