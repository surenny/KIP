import { Routes, Route, NavLink, Navigate } from 'react-router-dom';
import { useProject, useProjects, useProjectSwitch } from './hooks/useApi';
import Overview from './views/Overview';
import LogViewer from './views/LogViewer';
import Nodes from './views/Nodes';

function ConnectionBanner({ isError }: { isError: boolean }) {
  if (!isError) return null;
  return (
    <div style={{
      background: '#dc3545', color: 'white', padding: '6px 16px',
      fontSize: '13px', textAlign: 'center', fontWeight: 500,
    }}>
      Cannot reach server — check that <code style={{ background: 'rgba(0,0,0,0.2)', padding: '1px 4px', borderRadius: 3 }}>
      ui/start.sh</code> is running
    </div>
  );
}

function ProjectSwitcher() {
  const { data: project } = useProject();
  const { data: projects } = useProjects();
  const switcher = useProjectSwitch();

  if (!projects || projects.length <= 1) {
    return (
      <span className="project-badge" title={project?.path}>
        {project?.name ?? '…'}
      </span>
    );
  }

  return (
    <select
      className="project-switcher"
      value={project?.path ?? ''}
      onChange={(e) => switcher.mutate(e.target.value)}
      disabled={switcher.isPending}
      title={project?.path}
    >
      {projects.map(p => (
        <option key={p.path} value={p.path}>{p.name}</option>
      ))}
    </select>
  );
}

export default function App() {
  const { isError } = useProject();

  return (
    <div className="app">
      <ConnectionBanner isError={isError} />
      <header className="header">
        <ProjectSwitcher />
        <nav className="header-nav">
          <NavLink to="/" className={({ isActive }) => `nav-link ${isActive ? 'active' : ''}`} end>Nodes</NavLink>
          <NavLink to="/overview" className={({ isActive }) => `nav-link ${isActive ? 'active' : ''}`}>Overview</NavLink>
          <NavLink to="/logs" className={({ isActive }) => `nav-link ${isActive ? 'active' : ''}`}>Logs</NavLink>
        </nav>
      </header>
      <main className="main-content">
        <Routes>
          <Route path="/" element={<Nodes />} />
          <Route path="/nodes" element={<Nodes />} />
          <Route path="/nodes/:id" element={<Nodes />} />
          <Route path="/overview" element={<Overview />} />
          <Route path="/logs" element={<LogViewer />} />
          <Route path="*" element={<Navigate to="/" replace />} />
        </Routes>
      </main>
    </div>
  );
}
