echo "sending notifications about broken build"

#Send us email
#I don't think this works on warfa, so I'm leaving it disabled
# cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" emullen@cs.washington.edu
# cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" jrw12@cs.washington.edu
# cat $1 | mail -s "[OEUF BUILD BOT] Build is Broken" spernste@cs.washington.edu

#Post in slack
curl -sf -XPOST \
     --data-urlencode "payload={\"channel\":\"#oeuf\",\"link_names\":1,\"text\":\"$(python -c 'import sys; print(sys.argv[1].replace("\"", "\\\""))' "$1")\"}" \
     'https://hooks.slack.com/services/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'


