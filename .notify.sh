echo "sending email about broken build"

cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" emullen@cs.washington.edu
cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" jrw12@cs.washington.edu
cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" spernste@cs.washington.edu



