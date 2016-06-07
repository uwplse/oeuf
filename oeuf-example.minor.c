= "$8"
"$1"('$2', '$1') : int -> int -> int
{
  return '$1';
}
"$2"('$2', '$1') : int -> int -> int
{
  var '$4', '$3';
  '$3' = builtin malloc(8) : int -> int;
  int32['$3'] = 1;
  int32['$3' + 4] = '$1';
  '$4' = int32[int32['$2' + 4]](int32['$2' + 4], '$3') : int -> int -> int;
  return '$4';
}
"$3"('$2', '$1') : int -> int -> int
{
  var '$5';
  '$5' = builtin malloc(20) : int -> int;
  int32['$5'] = "$2";
  int32['$5' + 4] = '$1';
  int32['$5' + 8] = int32['$2' + 4];
  int32['$5' + 12] = int32['$2' + 8];
  int32['$5' + 16] = int32['$2' + 12];
  return '$5';
}
"$4"('$2', '$1') : int -> int -> int
{
  var '$6';
  '$6' = builtin malloc(16) : int -> int;
  int32['$6'] = "$3";
  int32['$6' + 4] = '$1';
  int32['$6' + 8] = int32['$2' + 4];
  int32['$6' + 12] = int32['$2' + 8];
  return '$6';
}
"$5"('$2', '$1') : int -> int -> int
{
  var '$11', '$10', '$9', '$8', '$7';
  '$7' = builtin malloc(12) : int -> int;
  int32['$7'] = "$1";
  int32['$7' + 4] = '$1';
  int32['$7' + 8] = int32['$2' + 4];
  '$8' = builtin malloc(12) : int -> int;
  int32['$8'] = "$4";
  int32['$8' + 4] = '$1';
  int32['$8' + 8] = int32['$2' + 4];
  '$9' = builtin malloc(12) : int -> int;
  int32['$9'] = "$7";
  int32['$9' + 4] = '$7';
  int32['$9' + 8] = '$8';
  '$10' = int32['$9']('$9', int32['$2' + 4]) : int -> int -> int;
  '$11' = int32['$10']('$10', '$1') : int -> int -> int;
  return '$11';
}
"$6"('$2', '$1') : int -> int -> int
{
  var '$12';
  '$12' = builtin malloc(8) : int -> int;
  int32['$12'] = "$5";
  int32['$12' + 4] = '$1';
  return '$12';
}
"$7"('$2', '$1') : int -> int -> int
{
  var '$16', '$15', '$14', '$13', '$17';
  {{ {{ '$1' = int32['$1'];
        switch (int32['$1']) {
          case 0: exit 2;
          case 1: exit 1;
          default: exit 2;

        }
        '$13' = int32[int32['$2' + 4]](int32['$2' + 4], int32['$1' + 4]) : 
        int -> int -> int;
        '$14' = builtin malloc(12) : int -> int;
        int32['$14'] = "$7";
        int32['$14' + 4] = int32['$2' + 4];
        int32['$14' + 8] = int32['$2' + 8];
        '$15' = int32['$14']('$14', int32['$1' + 4]) : int -> int -> int;
        '$16' = int32['$13']('$13', '$15') : int -> int -> int;
        '$17' = '$16';
        exit 1;
     }}
     '$17' = int32['$2' + 8];
     exit 0;
  }}
  return '$17';
}
"$8"('$2', '$1') : int -> int -> int
{
  var '$18';
  '$18' = builtin malloc(4) : int -> int;
  int32['$18'] = "$6";
  return '$18';
}
extern "$5000" = extern "__i64_dtos" : float -> long
extern "$5001" = extern "__i64_dtou" : float -> long
extern "$5002" = extern "__i64_stod" : long -> float
extern "$5003" = extern "__i64_utod" : long -> float
extern "$5004" = extern "__i64_stof" : long -> single
extern "$5005" = extern "__i64_utof" : long -> single
extern "$5006" = extern "__i64_sdiv" : long -> long -> long
extern "$5007" = extern "__i64_udiv" : long -> long -> long
extern "$5008" = extern "__i64_smod" : long -> long -> long
extern "$5009" = extern "__i64_umod" : long -> long -> long
extern "$5010" = extern "__i64_shl" : long -> int -> long
extern "$5011" = extern "__i64_shr" : long -> int -> long
extern "$5012" = extern "__i64_sar" : long -> int -> long

