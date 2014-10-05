import re

try:
    while True:
        msg = input().strip()
        if msg.startswith('Agda2>'):
            continue

        elif msg == '(agda2-highlight-clear)':
            continue

        elif msg.startswith('(agda2-highlight-load-and-delete-action'):
            continue

        elif msg.startswith('(agda2-info-action'):
            if '"*Type-checking*"' in msg:
                continue

            elif '"*Error*"' in msg:
                raw_error_msg = re.match(r'\(agda2-info-action "\*Error\*" "(.*)" nil\)', msg)
                error_msg_list = raw_error_msg.group(1).replace(r'\n', '\n').splitlines()

                line_len = max([len(i) for i in error_msg_list]) + 1

                print('\033[1;31m+==== Error '+ '='*(line_len-11) +'\033[m')
                for i in error_msg_list:
                    print('\033[1;31m|\033[m', i)
                print('\033[1;31m+'+ '='*line_len +'\033[m')

            elif '"*All Goals*"' in msg:
                raw_goal_msg = re.match(r'\(agda2-info-action "\*All Goals\*" "(.*)" nil\)', msg)
                goal_msg_list = raw_goal_msg.group(1).replace(r'\n', '\n').splitlines()
                line_len = max([len(i) for i in goal_msg_list]) + 1

                print('\033[1;32m+==== Goals '+ '='*(line_len-11) +'\033[m')
                for i in goal_msg_list:
                    i = re.sub(r'\?([1234567890])', '\033[1;31m?\g<1>\033[m', i)
                    i = re.sub(r'→', '\033[1;32m→\033[m', i)
                    print('\033[1;32m|\033[m', i)
                print('\033[1;32m+'+ '='*line_len +'\033[m')

            else:
                print('====', msg, '====')

            continue

        print(msg)

except:
    pass
