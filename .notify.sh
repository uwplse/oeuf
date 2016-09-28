echo "sending notifications about broken build"

#Send us email
BODY="Oeuf build is broken. See log at: http://oeuf.uwplse.org/logs/$1"

echo $BODY | mail -s "[OEUF BUILD BOT] Build is Broken" emullen@cs.washington.edu
echo $BODY | mail -s "[OEUF BUILD BOT] Build is Broken" jrw12@cs.washington.edu
echo $BODY | mail -s "[OEUF BUILD BOT] Build is Broken" spernste@cs.washington.edu


#Post in slack
#credit to Calvin for this
curl -sf -XPOST \
     --data-urlencode "payload={\"channel\":\"#oeuf\",\"link_names\":1,\"text\":\"$(python -c 'import sys; print(sys.argv[1].replace("\"", "\\\""))' "Build Broken")\"}" \
     'https://hooks.slack.com/services/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'


