from tweepy.streaming import StreamListener
from tweepy import OAuthHandler
from tweepy import Stream


#these should maybe not be human readable....
consumer_key="9obTjIrc4mtpY8uKOjCdvugp5"
consumer_secret="PPNhjCh2J0FL7bhuL0YsqaIlD1ktfRzG5V2fOu4aSgSVbO2x4d"
access_token="806704116168728576-v5AC7IXmIwS3JrkebE6JOViI4fRTQN8"
access_token_secret="2gAjcabmdnZh13AEHv8ISNMfgCZCVBwBrnyODuu8VuILw"

def parse_tweet(data) :
    #TODO: this method turns giant mess of unicode
    #into dictionary containing useful information
    return data

def call_oeuf(args) :
    #TODO: this calls Oeuf as a command line program
    #probably easiest way to do this
    return args

def send_tweet(txt,src_tweet) :
    pass

class StdOutListener(StreamListener):
    """ A listener handles tweets that are received from the stream.
    This is a basic listener that just prints received tweets to stdout.
    """
    def on_data(self, data):
        tweet = parse_data(data)
        result = call_oeuf(tweet)
        send_tweet(result, tweet)
        return True

    def on_error(self, status):
        print "error: "
        print(status)

if __name__ == '__main__':
    l = StdOutListener()
    auth = OAuthHandler(consumer_key, consumer_secret)
    auth.set_access_token(access_token, access_token_secret)
    stream = Stream(auth, l)
    stream.filter(track=['uwplse'])


if __name__ == "__main__":
    main()
