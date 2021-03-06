
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = "NAME NUMBERstart : '(' NAME ',' quan other_quan ':' dep other_dep ')' frac : expr '/' exprinterval : '[' expr ',' expr ']'expr : '-' exprexpr : NUMBERexpr : NAMEpartitioning : NUMBER\n                    | '(' frac other_frac ')' domain : interval\n              | set_of_valset_of_val : '{' expr other_val '}'quan : '{' NAME ',' interval ',' partitioning '}'dep : '{' NAME ',' domain '}'empty :other_quan : ',' quan other_quan\n                  | emptyother_dep : ',' dep other_dep\n                  | emptyother_frac : ',' frac other_frac\n                  | emptyother_val : ',' expr other_val\n                  | empty"
    
_lr_action_items = {'(':([0,23,],[2,33,]),'$end':([1,29,],[0,-1,]),'NAME':([2,6,16,18,25,33,34,37,48,50,53,],[3,10,22,27,27,27,27,27,27,27,27,]),',':([3,5,10,11,15,17,22,24,26,27,28,35,41,42,45,46,51,56,57,59,],[4,7,13,7,19,23,30,34,-5,-6,19,-4,-12,48,53,-13,-3,48,-2,53,]),'{':([4,7,12,19,30,],[6,6,16,16,37,]),':':([5,8,9,11,14,41,],[-14,12,-16,-14,-15,-12,]),'[':([13,30,],[18,18,]),')':([15,20,21,26,27,28,35,36,42,46,47,49,56,57,60,],[-14,29,-18,-5,-6,-14,-4,-17,-14,-13,55,-20,-14,-2,-19,]),'-':([18,25,33,34,37,48,50,53,],[25,25,25,25,25,25,25,25,]),'NUMBER':([18,23,25,33,34,37,48,50,53,],[26,32,26,26,26,26,26,26,26,]),'/':([26,27,35,43,],[-5,-6,-4,50,]),']':([26,27,35,44,],[-5,-6,-4,51,]),'}':([26,27,31,32,35,38,39,40,45,51,52,54,55,58,59,61,],[-5,-6,41,-7,-4,46,-9,-10,-14,-3,58,-22,-8,-11,-14,-21,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'start':([0,],[1,]),'quan':([4,7,],[5,11,]),'other_quan':([5,11,],[8,14,]),'empty':([5,11,15,28,42,45,56,59,],[9,9,21,21,49,54,49,54,]),'dep':([12,19,],[15,28,]),'interval':([13,30,],[17,39,]),'other_dep':([15,28,],[20,36,]),'expr':([18,25,33,34,37,48,50,53,],[24,35,43,44,45,43,57,59,]),'partitioning':([23,],[31,]),'domain':([30,],[38,]),'set_of_val':([30,],[40,]),'frac':([33,48,],[42,56,]),'other_frac':([42,56,],[47,60,]),'other_val':([45,59,],[52,61,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> start","S'",1,None,None,None),
  ('start -> ( NAME , quan other_quan : dep other_dep )','start',9,'p_start','parser.py',49),
  ('frac -> expr / expr','frac',3,'p_frac','parser.py',57),
  ('interval -> [ expr , expr ]','interval',5,'p_interval','parser.py',61),
  ('expr -> - expr','expr',2,'p_expr_uminus','parser.py',65),
  ('expr -> NUMBER','expr',1,'p_expr_number','parser.py',69),
  ('expr -> NAME','expr',1,'p_expr_name','parser.py',73),
  ('partitioning -> NUMBER','partitioning',1,'p_partitioning','parser.py',77),
  ('partitioning -> ( frac other_frac )','partitioning',4,'p_partitioning','parser.py',78),
  ('domain -> interval','domain',1,'p_domain','parser.py',85),
  ('domain -> set_of_val','domain',1,'p_domain','parser.py',86),
  ('set_of_val -> { expr other_val }','set_of_val',4,'p_set_of_val','parser.py',90),
  ('quan -> { NAME , interval , partitioning }','quan',7,'p_quan','parser.py',94),
  ('dep -> { NAME , domain }','dep',5,'p_dep','parser.py',98),
  ('empty -> <empty>','empty',0,'p_empty','parser.py',103),
  ('other_quan -> , quan other_quan','other_quan',3,'p_other_quan','parser.py',113),
  ('other_quan -> empty','other_quan',1,'p_other_quan','parser.py',114),
  ('other_dep -> , dep other_dep','other_dep',3,'p_other_dep','parser.py',118),
  ('other_dep -> empty','other_dep',1,'p_other_dep','parser.py',119),
  ('other_frac -> , frac other_frac','other_frac',3,'p_other_frac','parser.py',123),
  ('other_frac -> empty','other_frac',1,'p_other_frac','parser.py',124),
  ('other_val -> , expr other_val','other_val',3,'p_other_val','parser.py',128),
  ('other_val -> empty','other_val',1,'p_other_val','parser.py',129),
]
