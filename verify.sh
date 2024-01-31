# /bin/sh

GOBRA_JAR="/Users/arquintlinard/ETH/PhD/gobra/target/scala-2.13/gobra.jar"
INPUT_FILES="\
    agent/session/datachannel/datachannel.go\
    agent/session/datachannel/handshake_complete.go\
    agent/session/datachannel/handshake_request.go\
    agent/session/datachannel/handshake_response.go\
    agent/session/datachannel/helper.go\
    agent/session/datachannel/init.go\
    agent/session/datachannel/recv.go\
    agent/session/datachannel/send_recv_channel.go\
    agent/session/datachannel/send.go\
    agent/session/datachannel/state.go"

java -Xss128m -jar $GOBRA_JAR \
    --module "github.com/aws/amazon-ssm-agent" \
    --include ".verification" --include "." \
    --input $INPUT_FILES
