import * as React from 'react';
import { useRpcSession, EnvPosContext, InteractiveMessageData } from '@leanprover/infoview';

export default function (props) {
  const pos = React.useContext(EnvPosContext);
  const rs = useRpcSession();

  const [value, setValue] = React.useState('');

  const [out, setOut] = React.useState(props.empty.response);
  const [err, setErr] = React.useState(props.empty.response);

  React.useEffect(() => {
    let run = true;
    async function pollOut(){
      while (run) {
        const res = await rs.call('Typewriter.recv', { pos: pos, channel: props.draftOut });
        setValue('');
        setErr(props.empty.response);
        setOut(res.response);
      }
    }
    async function pollErr() {
      while (run) {
        const res = await rs.call('Typewriter.recv', { pos: pos, channel: props.draftErr });
        setErr(res.response);
      }
    }

    pollOut();
    pollErr();

    return () => {
      run = false;
    };
  }, []);

  const onEnter = async (e) => {
    e.preventDefault();
    await rs.call('Typewriter.send', { pos: pos, text: value, channel: props.draftIn });
  };

  return React.createElement(
    'form',
    { onSubmit: onEnter },
    React.createElement(InteractiveMessageData, {"msg": out}),
    React.createElement('br'),
    React.createElement(InteractiveMessageData, {"msg": err}),
    React.createElement('br'),
    React.createElement('input', {
      type: 'text',
      value: value,
      onChange: (e) => setValue(e.target.value),
      placeholder: 'Type something and press Enter…',
    })
  );
}