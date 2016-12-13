from tweepy.streaming import StreamListener
from tweepy import OAuthHandler
from tweepy import Stream
from tweepy import API
import json
import subprocess 

#these should maybe not be human readable....
#try not to show on screen for too long if showing live demo
consumer_key="9obTjIrc4mtpY8uKOjCdvugp5"
consumer_secret="PPNhjCh2J0FL7bhuL0YsqaIlD1ktfRzG5V2fOu4aSgSVbO2x4d"
access_token="806704116168728576-v5AC7IXmIwS3JrkebE6JOViI4fRTQN8"
access_token_secret="2gAjcabmdnZh13AEHv8ISNMfgCZCVBwBrnyODuu8VuILw"
global api

OOM = "Due to my unary representation of numbers, I ran out of address space"

def parse_tweet(data) :
    dic = json.loads(data)
    return dic

def call_oeuf(args) :
    oeuf = subprocess.Popen(["/home/emullen/oeuf/list_demo"] + args, stdout=subprocess.PIPE)
    out, err = oeuf.communicate()
    if out == "": #list_demo will always print something unless it segfaults
        return OOM
    return out

def send_tweet(txt,user,tweet_id) :
    if txt == OOM:
        tweet = "@" + user + " " + OOM
    else:
        tweet = "@" + user + " the largest number in your last tweet was: " + txt
    print tweet
    try:
        api.update_status(tweet,tweet_id)
    except:
        pass
    
#turn any tweet into a list of numbers
def sanitize(x):
    words = x.split()
    l = []
    for word in words:
        try:
            n = str(int(word))
            l = l + [n]
        except:
            pass
    return l
    
class StdOutListener(StreamListener):
    """ A listener handles tweets that are received from the stream.
    This is a basic listener that just prints received tweets to stdout.
    """
    def on_data(self, data):
        tweet = parse_tweet(data)
        sanitary = sanitize(tweet["text"])
        if len(sanitary) > 0:
            user = tweet["user"]["screen_name"]
            result = call_oeuf(sanitary)
            send_tweet(result,user,tweet["id"])
        return True

    def on_error(self, status):
        print "error: "
        print(status)

        
if __name__ == '__main__':
    global api
    l = StdOutListener()
    auth = OAuthHandler(consumer_key, consumer_secret)
    auth.set_access_token(access_token, access_token_secret)
    api = API(auth)
    stream = Stream(auth, l)
    stream.filter(track=['@oeufbot'])


