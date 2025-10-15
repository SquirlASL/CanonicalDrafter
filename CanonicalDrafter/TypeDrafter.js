import * as React from 'react';
import { useRpcSession, EditorContext, EnvPosContext } from '@leanprover/infoview';

export default function (props) {
  const pos = React.useContext(EnvPosContext);
  const rs = useRpcSession();

  const [value, setValue] = React.useState('');

  const [out, setOut] = React.useState('');
  const [err, setErr] = React.useState('');

  React.useEffect(() => {
    let run = true;
    async function pollOut(){
      while (run) {
        const res = await rs.call('Typewriter.recv', { pos: pos, channel: props.draftOut });
        setValue('');
        setErr('');
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
    React.createElement('p', null, out),
    React.createElement('p', { style: { color: 'red' } }, err),
    React.createElement('input', {
      type: 'text',
      value: value,
      onChange: (e) => setValue(e.target.value),
      placeholder: 'Type something and press Enter…',
    })
  );
}